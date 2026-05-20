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