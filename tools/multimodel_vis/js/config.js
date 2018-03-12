require.config({
    baseUrl: "/",
    // Per: http://stackoverflow.com/questions/8315088/prevent-requirejs-from-caching-required-scripts
    // urlArgs: "bust=" + (new Date()).getTime(),
    paths: {
        // External/3rd-party libraries
        'jquery':           'lib/jquery-3.1.0.min',
        // 'bootstrap':        'lib/bootstrap-3.3.7-dist/js/bootstrap.min',
        'underscore':       'lib/underscore-min',
        // 'backbone':         'lib/backbone-min',
        'text':             'lib/text',
        // 'uuid':             'lib/uuid',
        // 'scroll-into-view': 'lib/jquery.scrollintoview.min',
        'cytoscape':        'lib/cytoscape.min',
        'cytoscape-cola':   'lib/cytoscape-cola',
        'cola':             'lib/cola.min',
        'cytoscape-panzoom': 'lib/cytoscape.js-panzoom-master/cytoscape-panzoom',
        // 'cytoscape-cxtmenu': 'lib/cytoscape.js-cxtmenu-master/cytoscape-cxtmenu',
        // 'leaflet':          'lib/leaflet/leaflet',
        'vis':              'lib/vis/vis.min',
        'd3':               'lib/d3/d3.min',
        // 'FileSaver':        'lib/FileSaver.min',
        'domReady':         'lib/domReady',
    },
    shim: {
        // 'bootstrap':   [ 'jquery' ],
        // 'backbone':    [ 'underscore' ],
        // 'scroll-into-view': [ 'jquery' ],
    }
});
