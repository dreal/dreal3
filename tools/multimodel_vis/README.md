Multi-Model Visualization with dReach
=====================================

This visualization replaces the one in the ODE_visualization
directory. It draws from that code, but replaces the CoffeeScript with
vanilla JavaScript, uses some additional libraries, and supports
multiple models.

Running the Vis
---------------

First, prepare a data.json file. This call merges the
```xxx.smt2.json``` and ```xxx.drh``` into a single
```data.json```. Note that this script expects the base name of the
```.drh``` file; it will dynamically determine the corresponding
```.json``` file.

```
$ ./prep_data.perl data/PROB-GOING-DOWNTOWN-LOW-FUEL-DISTRACTED-DRIVER_bjuxfo57-tmp
```

Then, run the webserver. This script determines whether the Python in
your path is version 2 or version 3 and then invokes it with the
correct parameters.

```
$ ./servefiles.perl
```

Finally, open a web browser to "http://localhost:8000/". You should
see the visualization.

