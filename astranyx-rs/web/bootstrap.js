// Bootstrap script for loading WASM module

async function init() {
    const loading = document.getElementById('loading');

    try {
        // Import the WASM module (built by wasm-pack)
        const wasm = await import('../pkg/astranyx_client.js');

        // Initialize the WASM module
        await wasm.default();

        // Hide loading indicator
        loading.classList.add('hidden');

        console.log('Astranyx initialized successfully');
    } catch (error) {
        console.error('Failed to initialize Astranyx:', error);
        loading.textContent = 'Failed to load: ' + error.message;
    }
}

// Check for WebGPU support
async function checkWebGPU() {
    if (!navigator.gpu) {
        const loading = document.getElementById('loading');
        loading.innerHTML = `
            <div style="text-align: center;">
                <p>WebGPU is not supported in your browser.</p>
                <p style="margin-top: 10px; font-size: 14px; color: #888;">
                    Try Chrome 113+, Edge 113+, or Firefox Nightly with WebGPU enabled.
                </p>
            </div>
        `;
        return false;
    }

    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) {
        const loading = document.getElementById('loading');
        loading.textContent = 'No WebGPU adapter found. Try updating your graphics drivers.';
        return false;
    }

    return true;
}

// Main entry point
(async () => {
    if (await checkWebGPU()) {
        await init();
    }
})();
