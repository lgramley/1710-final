// Setup for importing necessary scripts/plugins
function loadSources() {
    var visImport = document.createElement('script');
    visImport.setAttribute('src', 'https://cdnjs.cloudflare.com/ajax/libs/vis/4.21.0/vis.min.js');
    document.head.appendChild(visImport);

    var styleSheet = document.createElement('link');
    styleSheet.setAttribute('rel', 'stylesheet');
    styleSheet.setAttribute('href', 'https://cdnjs.cloudflare.com/ajax/libs/vis/4.21.0/vis.min.css');
    document.head.appendChild(styleSheet);
}

// Function to initialize visualization
function initVisualization() {
    var nodes = new vis.DataSet([
        { id: 1, label: 'Driver', shape: 'ellipse' },
        { id: 2, label: 'Passenger', shape: 'ellipse' }
    ]);

    var edges = new vis.DataSet([]);

    var container = document.getElementById('visualization-container');
    var data = { nodes: nodes, edges: edges };
    var options = {};
    var network = new vis.Network(container, data, options);
}

// Clear previous content
document.getElementById('visualization-container').innerHTML = '';

// Load sources and initialize visualization
loadSources();
// setTimeout(initVisualization, 1000); // Delay for sources to load
