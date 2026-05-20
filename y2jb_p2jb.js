[...]
327|             ;(function self_test() {
[...]
1586|         function exploit_sleep_10ms() { nanosleep_safe(TS_10MS); }
1587|         function exploit_sleep_50ms() { nanosleep_safe(TS_50MS); }
1588|         function exploit_sleep_100ms() { nanosleep_safe(TS_100MS); }
1589|         function exploit_sleep_1sec() { nanosleep_safe(TS_1SEC); }
1590|         function exploit_sleep_3sec() { nanosleep_safe(TS_3SEC); }
[...]
2710|         function hw_mfence() { if (f_mfence) f_mfence(); }
2711|         function hw_sfence() { if (f_sfence) f_sfence(); }
2712|         function hw_lfence() { if (f_lfence) f_lfence(); }
[...]
2856|             function p(v) { write64(cb + idx * 8n, BigInt(v)); idx++; }
[...]
3743|         function kread32(kaddr) { kread(scratch_big, BigInt(kaddr), 4n); return read32(scratch_big); }
3744|         function kread64(kaddr) { kread(scratch_big, BigInt(kaddr), 8n); return read64(scratch_big); }
3745|         function kwrite32(kaddr, val) { write32(scratch_big, BigInt(val)); kwrite(BigInt(kaddr), scratch_big, 4n); }
3746|         function kwrite64(kaddr, val) { write64(scratch_big, BigInt(val)); kwrite(BigInt(kaddr), scratch_big, 8n); }
[...]
3758|         function get_file_ptr(fd) { return kread64(fd_ofiles + BigInt(fd) * runtime_offsets.FILEDESCENT_SIZE); }
[...]
3767|         function null_socket_rthdr(fd) {
[...]
// Integration of the new synchronization methods
function create_worker_sync(count) {
    let aligned = new Array(count).fill(0);
    return {
        cmd: 0,
        finished: aligned,
        total: count,
        gen: 0
    };
}

function signal_workers(ws) {
    ws.gen++;
    for (let i = 0; i < ws.total; i++) {
        ws.finished[i] = 0;
    }
    ws.cmd = ws.gen;
    // Simulate waking workers
    console.log(`Workers signaled with gen ${ws.gen}`);
}

function wait_workers(ws) {
    return new Promise(resolve => {
        const checkWorkers = () => {
            if (ws.finished.every(val => val !== 0)) {
                resolve();
            } else {
                setTimeout(checkWorkers, 10); // adjust delay for efficiency
            }
        };
        checkWorkers();
    });
}

// Usage example (pseudo-code):
(async () => {
    let workers = create_worker_sync(5);
    signal_workers(workers);
    console.log("Waiting for workers to complete...");
    await wait_workers(workers);
    console.log("All workers completed!");
})();