dOp: delta-complete Optimizer
=============================

Input Format (`.dop` file)
--------------------------

Let's first take an example:

```
var:
    x : [-5,5]
    y : [-5,5]

cost:
    y * sin(x)

ctr:
    0.6 < cos(x) + y
    3.5 > x * exp(y)
```

`.dop` format consists of three sections:

 - `var:` section declares a set of variables and their bounded
   domains. In the above example, `x : [-5, 5]` declares a Real
   variable `x` whose domain is an interval `[-5, 5]`.

 - `cost:` section specifies a cost function that the tool will
   minimize. In the above example, dOp tool will find a solution `(x,
   y)` which minimizes the given cost function `f(x, y) = y * sin(x)`.

 - `ctr:` is an optional section which specifies a set of constraints
   that an optimal solution has to satisfy. In the above example, we
   added two constraints - `0.6 < cos(x) + y` and `3.5 > x * exp(y)`.

Output
------

Let's save the above example to `example.dop` file and run it with
`--save-visualization` option:

```bash
./dOp example.dop --save-visualization
```

It will output the following:

```
Precision  : 0.001
Variable   : min in [-inf, inf]
Variable   : x in [-5, 5]
Variable   : y in [-5, 5]
Minimize   : (* y (sin x))
Constraint : (not (<= (+ (cos x) y) 0.6))
Constraint : (not (<= 3.5 (* x (exp y))))
Result     : delta-sat
    x = [-1.58884, -1.58827]
    y = [4.99995, 5]
    min = [-4.99924, -4.99919]
Visualization Code is saved at example_01.dop.py
```

It found a small enough interval box `x = [-1.58884, -1.58827]` and `y
= [4.99995, 5]`. The tool claims that this box minimizes the given
cost function `f(x, y) = y * sin(x)` so that it's bounded to
`[-4.99924, -4.99919]`.

The used option `--save-visualization` saves a python code to
`example_01.dop.py` which can be run to visualize a given cost
function and a found solution.


How to Run Visualization
------------------------

Visualization code is written in [Python2][python2] using
[matplotlib][matplotlib] library. We recommend you to run the
following to install required packages locally using [virtualenv][virtualenv]

```bash
virtualenv env
. env/bin/activate # you should do it every time!
pip install -r <path_to_dreal3>/src//tools/dop/requirements.txt
```

Once you install the required packages, it is easy to execute the
visualization script.

```
(env) $ python example1.dop.py
```

You should see the following screenshot:

![screen shot 2015-08-21 at 12 25 23 am](https://cloud.githubusercontent.com/assets/403281/9401292/2c3cdda4-479b-11e5-9ef7-74e41dc2879c.png)

[python2]: https://www.python.org
[matplotlib]: http://matplotlib.org
[virtualenv]: https://virtualenv.pypa.io/en/latest


dOp Options
-----------

 - `-h`, `-help`, `--help`, `--usage`: Display usage instructions.
 - `-precision ARG`: Set precision (default 0.001), this overrides the value specified in input files.
 - `--run-vis`, `--run-visualization`: Visualize the result
 - `--save-vis`, `--save-visualization`: Save Python visualization code
 - `--vis-cell ARG`: Set the number of cells in grid (in visualization)
