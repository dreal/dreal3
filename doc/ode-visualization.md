How to use ODE visualization
============================

Running dReal with ``--visualize`` option generates ``<xxx.smt2.json>`` if the result is ``SAT``. The ``.json`` file contains an ODE trajectory witnessing the satisfiable assignment.

 - Copy the generated ``.json`` file to  ``dreal/tools/ODE_visualization`` directory, renaming it to
    ``data.json``.

````
    cd ~/dreal/tools/ODE_visualization
    cp <path_to_xxx.smt2.json> data.json
````

 - Run Webserver

````
    ./run_websvr.sh
````

 - Open a URL ``http://localhost:8000`` with an web browser.

````
    google-chrome http://localhost:8000
````

Customizing Visualization
=========================

By modifying [tools/ODE_visualization/index.html](/tools/ODE_visualization/index.html) file, you can customize the visualization:

````js
var config = {
    jsonfile : 'data.json',
    animation_delay : 800,
    width : 950,
    height : 800,
    inter_chart_margin: 20,
    contextHeight : 300,
    margin : {top: 50, right: 40, bottom: 50, left: 60}
}
````


