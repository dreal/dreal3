require([
    'jquery',
    'underscore',

    'vis',
    'd3',

    'cytoscape',
    'cytoscape-panzoom',
    'cytoscape-cola',
    'cola',
    'text!css/graph-style.css',

    'text!data.json',

    // But don't go until we're ready.
    'domReady'
], function($, _,
            Vis, d3,
            cytoscape,
            cyPanzoom,
            cyCola,
            cola,
            graphStyle,
            dataText) {

    // Register the pan-zoom plug-in.
    cyCola(cytoscape, cola);
    cyPanzoom(cytoscape, $);

    // Regex for getting variable name from a piece key.
    var variableRegex = /^(.*?)_\d+_\d+$/;

    // Hash of assigned colors. Seeded with fixed colors.
    var hueForState = {
        on: 120.0,
        off: 0.0,
    };
    var assignedStateCount = 0;

    // When true, the timeline will assign subgroups based on modes,
    // making the graph tall, but making it easy to see recurring
    // modes.
    //
    // After setting this, you must call populateTimeline to see the
    // effect.
    var useSubgroups = false;

    // When true, the timeline will show individual steps along the
    // x-axis. When false, the timeline will compute and use time in
    // seconds. Time in seconds is a more accurate reflection of the
    // real world, but makes instantaneous transitions hard or
    // impossible to see.
    //
    // After setting this, you must call populateTimeline to see the
    // effect.
    var useSteps = false;

    // Prepare the data.
    // console.log(dataText);
    var data = JSON.parse(dataText);
    var modes = data.modes || [];
    var traces = data.traces || [];

    // Here are some values derived from the data. These are used for
    // scaling and clipping the graph. Note that we *could* do
    // something complicated wherein these values are set dynamically
    // from user interaction (say, zooming in).
    var minTime = 0.0;
    var maxTime = 1.0;
    var minY = 0.0;
    var maxY = 1.0;

    var modesByStep = getModesByStep(modes);
    var tracesByStep = getTracesByStep(traces, modesByStep);
    console.log('Got some traces by step', tracesByStep);

    // There is a contiguous array of steps...
    var minStep = 0;
    var maxStep = tracesByStep.length;

    // Set up the UI stuff.
    updateUI();

    // ------------------------------------------------------------
    // Set up event handling.
    $('#use-subgroups').click(function() {
        if (!useSubgroups) {
            useSubgroups = true;
            updateUI();
        }
    });
    $('#not-use-subgroups').click(function() {
        if (useSubgroups) {
            useSubgroups = false;
            updateUI();
        }
    });
    $('#toggle-subgroups').click(function() {
        useSubgroups = !useSubgroups;
        updateUI();
    });

    $('#use-steps').click(function() {
        if (!useSteps) {
            useSteps = true;
            updateUI();
        }
    });
    $('#use-times').click(function() {
        if (useSteps) {
            useSteps = false;
            updateUI();
        }
    });
    $('#toggle-steps-times').click(function() {
        useSteps = !useSteps;
        updateUI();
    });

    // ------------------------------------------------------------

    function updateUI() {
        // For now, just redraw the entire element.s
        populateTimeline();
        populateOdeGraph();
        populateAutomata();
    }

    // ------------------------------------------------------------
    // Timeline

    function populateTimeline() {

        // This is where the timeline will go.
        var container = $('#timeline-container')[0];
        if (!container) {
            return;
        }
        $(container).html('');

        // Populate the the datasets for the timeline.
        var groups = new Vis.DataSet();
        var items = new Vis.DataSet();

        var minTime = Number.MAX_VALUE;
        var maxTime = Number.MIN_VALUE;

        var lastItem = {};
        // var now = new Date();

        $.each(modesByStep, function(step, stepObj) {
            if (!stepObj) {
                return;
            }

            var startTime = stepObj.startTime;
            var endTime = stepObj.endTime;
            if (undefined === startTime) {
                console.warn('Step ' + step + ' does not have start time.', stepObj);
            }
            if (undefined === endTime) {
                console.warn('Step ' + step + ' does not have end time.', stepObj);
            }

            $.each(stepObj, function(automatonId, automatonObj) {
                if (!$.isPlainObject(automatonObj) ||
                    (undefined === automatonObj.modeLabel)) {
                    return;
                }

                // If necessary, add the group.
                if (!groups.get(automatonId)) {
                    groups.add({
                        id: automatonId,
                        content: automatonObj.label,
                        subgroupOrder: 'subgroup',
                    });
                }

                // Add a new item or extend the previous one.
                var start;
                var end;
                if (useSteps) {
                    start = step;
                    end = step + 1;
                } else {
                    start = //now.getMilliseconds() +
                        1000.0 * startTime;
                    end = //now.getMilliseconds() +
                        1000.0 * endTime;
                }

                var itemId = '' + automatonId + '_' + step;
                var item = lastItem[automatonId];

                var className = '' + automatonId +
                    '-' + automatonObj.modeLabel;

                // Look up mode label information for this state.
                var modeLabelObj = getModeLabel(automatonObj);
                // var shortLabel = automatonObj.modeLabel;
                // shortLabel = shortLabel.replace(/s0+(\d+?)/, "s$1");
                if (!item ||
                    automatonObj.changed) {
                    // Add a new item.
                    item = {
                        id: itemId,
                        title: modeLabelObj.title,
                        // automatonObj.modeLabel,
                        // + ' [' + start + ', ' + end + ']',
                        content: modeLabelObj.content,
                        // shortLabel,
                        group: automatonId,
                        start: start,
                        end: end,

                        className: className,
                    };
                    // Hrm. If we use this it defines the color in the
                    // style attribute of the element. This takes
                    // precedence over css classes, this breaking the
                    // highlight on hover.
                    //
                    item.style = getTimelineColorStyle(automatonObj.modeLabel);

                    // When using subgroups, each mode gets its own
                    // row in the timeline. This looks nice but takes
                    // a lot of vertical space.
                    if (useSubgroups) {
                        item.subgroup = automatonObj.modeId;
                    }

                    items.add(item);

                    lastItem[automatonId] = item;
                } else {
                    // Extend the previous item.
                    item.end = end;
                    item.title = modeLabelObj.title,
                    // automatonObj.modeLabel;
                    // + ' [' + item.start + ', ' + item.end + ']',

                    // And update the item in the dataset, so that the
                    // change sticks.
                    items.update(item);
                }

                if (start < minTime) {
                    minTime = start;
                }
                if (end > maxTime) {
                    maxTime = end;
                }
            });
        });

        var options = {
            stack: false,
            showMajorLabels: false,
            min: minTime,
            max: maxTime,

            moveable: true,
            zoomable: true,
            clickToUse: true,
        };
        var timeline = new Vis.Timeline(container, items, groups, options);

        // Add some event handlers to do dynamic stuff.
        timeline.on('itemover', function(e) {
            var item = items.get(e.item);
            // console.log('Mouse is over: ', item);
            $('.' + item.className).addClass("drh-highlight");
        });
        timeline.on('itemout', function(e) {
            // console.log('Mouse left: ', e.item);
            // Remove the highlight class from everything.
            $(".drh-highlight").removeClass("drh-highlight");
        });
    }

    function getModeLabel(automatonObj) {
        // Choose sensible defaults in case we cannot find the drh
        // model data.
        var shortLabel = automatonObj.modeLabel;
        shortLabel = shortLabel.replace(/s0+(\d+?)/, "s$1");
        var modeLabel = {
            // The content of the bar.
            content: shortLabel,
            // The stuff shown in the onhover tooltip.
            title: automatonObj.modeLabel,
        };

        // Get the model and then the state label.
        var model = findModel(automatonObj.label);
        var stateData;
        if (model &&
            model.modes) {
            // Found the model, get the state information and form a
            // label from it.
            // console.log("Look for state information for: " + automatonObj.modeLabel,
            //             model);
            stateData = model.modes[automatonObj.modeLabel];
        }

        if (stateData) {
            // console.log("Found state data, make a label.", stateData);
            if (stateData.label) {
                modeLabel.content = stateData.label;
            }

            if (stateData.features) {
                modeLabel.title = stateData.features;
            }
        }

        return modeLabel;
    }

    function findModel(modelLabel) {
        if (!data ||
            !data.drh) {
            return;
        }

        var rawModelLabel = modelLabel;
        rawModelLabel = rawModelLabel.replace(/\d+$/, "");

        var model;
        $.each(data.drh, function(modelName, modelData) {
            if (!model &&
                (modelName === rawModelLabel)) {
                // Whee... we found the actual model.
                // console.log("Found model for " + modelLabel + " => " + rawModelLabel);
                model = modelData;
            }
        });

        return model;
    }

    // ------------------------------------------------------------
    // ODE Graph

    // Object with keys = variable name and value =
    // 0 - default visibility
    // 1 - selected
    var knownOdeVars;

    // Here is a useful SVG line graph example:
    // http://bl.ocks.org/mbostock/3883245
    function populateOdeGraph() {
        // Reset the graph before we get started.
        $('#ode-graph-container').html('');
        $('#ode-variable-list').html('');
        knownOdeVars = {};

        // Per this example, define some margins, use these plus the
        // graph dimensions to set up the scales.
        // http://bl.ocks.org/mbostock/1550e57e12e73b86ad9e
        var svgWidth = $('#ode-graph-container').width();
        var svgHeight = $('#ode-graph-container').height();
        var margin = {
            top: 20,
            left: 50,
            bottom: 30,
            right: 20,
        };
        var graphWidth = svgWidth - margin.left - margin.right;
        var graphHeight = svgHeight - margin.top - margin.bottom;

        // Set up the SVG area.
        var svg = d3.select('#ode-graph-container')
            .append('svg')
            .attr('width', svgWidth)
            .attr('height', svgHeight);

        // Translate everything so that it is drawn from the graph
        // origin.
        var graphContent = svg.append('g')
            .attr('transform',
                  'translate(' +
                  margin.left + ', ' + margin.top +
                  ')');

        // Define the x and y scales. Use these to position points in
        // the graph space.
        var xScale = d3.scaleLinear()
            .range([0, graphWidth]);
        // Define the domain. Always anchor to zero so that our graph
        // is grounded. We could choose minStep/minTime later on.
        if (useSteps) {
            xScale.domain([0, maxStep]);
        } else {
            xScale.domain([0.0, maxTime]);
        }

        var yScale = d3.scaleLinear()
            .range([0, graphHeight]);
        yScale.domain([maxY, 0.0]);

        // Loop over the steps, drawing stuff for each one.
        $.each(tracesByStep, function(step, stepObj) {
            // Draw vertical lines separating steps first, so that
            // real data can go on top when necessary.
            var stepBoundaryLine;
            var stepX;
            if (0 !== step) {
                if (useSteps) {
                    stepX = step;
                } else {
                    stepX = stepObj.startTime;
                }
                stepBoundaryLine = d3.line()
                    .x(function(d) { return xScale(d[0]); })
                    .y(function(d) { return yScale(d[1]); });
                graphContent.append('path')
                    .datum([ [stepX, 0],
                             [stepX, maxY] ])
                    .style('stroke-width', '0.5px')
                    .style('stroke', '#999999')
                    .attr('d', stepBoundaryLine);
            }

            // Draw a line for each piece in this step.
            $.each(stepObj, function(pieceName, pieceObj) {
                // console.log(j, pieceObj);
                if (!pieceObj.values) {
                    // No need to warn here. The piece has automaton
                    // modes as well as piece values, so this is normal.
                    //
                    // console.log("No values to graph, skipping.");
                    return;
                }
                var stepDuration = stepObj.endTime - stepObj.startTime;
                // If the step had no duration, just
                // return. Alternatively, we could add code to plot
                // horizontal lines a the y value.
                if (0 === stepDuration) {
                    return;
                }

                // We'll use this for both the line and the area.
                var hue = getHueFor(pieceName);

                var piece = graphContent.append('g')
                    .attr('class', pieceName);

                // console.log("Num values = " + numValues);
                var line = d3.line()
                    .x(function(d) {
                        // console.log("d:", d);
                        var val = (d.time[0] + d.time[1]) * 0.5;
                        if (useSteps) {
                            val = step + (val - stepObj.startTime) / stepDuration;
                        }
                        // console.log("returning x value: " + val);
                        return xScale(val);
                    })
                    .y(function(d) {
                        var val = (d.enclosure[0] + d.enclosure[1]) * 0.5;
                        // console.log("d: " + d + " returning y value: " + val);
                        return yScale(val);
                    });
                piece.append('path')
                    .datum(pieceObj.values)
                    .style('stroke-width', '1.5px')
                    .style('stroke', d3.hsl(hue, 0.5, 0.6))
                    .attr('d', line);

                var area = d3.area()
                    .x0(function(d) {
                        // console.log("d:", d);
                        var val = d.time[0];
                        if (useSteps) {
                            val = step + (val - stepObj.startTime) / stepDuration;
                        }
                        // console.log("returning x value: " + val);
                        return xScale(val);
                    })
                    .x1(function(d) {
                        // console.log("d:", d);
                        var val = d.time[1];
                        if (useSteps) {
                            val = step + (val - stepObj.startTime) / stepDuration;
                        }
                        // console.log("returning x value: " + val);
                        return xScale(val);
                    })
                    .y0(function(d) {
                        var val = d.enclosure[0];
                        // console.log("d: " + d + " returning y value: " + val);
                        return yScale(val);
                    })
                    .y1(function(d) {
                        var val = d.enclosure[1];
                        // console.log("d: " + d + " returning y value: " + val);
                        return yScale(val);
                    });

                piece.append('path')
                    .datum(pieceObj.values)
                    .style('fill', d3.hsl(hue, 0.5, 0.8, 0.6))
                    .attr('d', area);

                // Add an entry for the ODE variable.
                addOdeVariable(pieceName);
            });
        });

        // Put the axes on top of the graph. By default, the xAxis
        // draws at the pixel origins (top-left), move it down to the
        // bottom of the graph.
        var xAxis = d3.axisBottom(xScale);
        graphContent.append('g')
            .attr('transform',
                  'translate(0, ' +
                  graphHeight +
                  ')')
            .call(xAxis);

        var yAxis = d3.axisLeft(yScale);
        graphContent.append('g')
            .call(yAxis);

        // Make sure all the variables are shown properly.
        updateVariableVisibility();
    }

    function addOdeVariable(varName) {
        if (undefined !== knownOdeVars[varName]) {
            // Already exists, just return.
            return;
        }
        var div = $('<div>').appendTo('#ode-variable-list');

        // Make a span with a non-breaking space, so that the height
        // makes sense.
        var colorBlock = $('<span>').appendTo(div);
        $(colorBlock).addClass('color-block');

        var hue = getHueFor(varName);
        $(colorBlock).css('background-color', d3.hsl(hue, 0.5, 0.8));
        $(colorBlock).css('border', '1px solid ' + d3.hsl(hue, 0.5, 0.6));

        div.append(varName);

        // Dunno what value to put here, but definitely somthing that
        // is defined.
        knownOdeVars[varName] = 0;

        // Add event handling for the color blocks.
        $(colorBlock).hover(function() {
            // console.log("Hover in: " + varName);
            $(div).addClass('selected');
            updateVariableVisibility(varName);
        }, function() {
            // If the var is selected, don't unselect it on hover-out.
            if (!knownOdeVars[varName]) {
                // console.log("Hover out: " + varName);
                $(div).removeClass('selected');
                updateVariableVisibility();
            }
        });

        $(colorBlock).click(function() {
            if (knownOdeVars[varName]) {
                // console.log("Clear selection of: " + varName);
                $(div).removeClass('selected');
                knownOdeVars[varName] = 0;
            } else {
                // console.log("Select: " + varName);
                $(div).addClass('selected');
                knownOdeVars[varName] = 1;
            }
            updateVariableVisibility();
        });
    }

    // Add code to show/hide vars. If set the focusVar is hovered and
    // should be shown accordingly.
    function updateVariableVisibility(focusVar) {
        // Loop over the known variables, making them visible or not.

        // Set the visibility for any selected vars.
        var selectedCount = 0;
        $.each(knownOdeVars, function(varName, varState) {
            if (varState ||
                (focusVar === varName)) {
                ++selectedCount;
                // console.log("Show var: " + varName);
                $('.' + varName).show();
            }
        });

        // Hide the unselected vars. If none of selected, show them
        // all.
        $.each(knownOdeVars, function(varName, varState) {
            if ((0 === varState) &&
                (focusVar !== varName)) {
                if (selectedCount) {
                    // console.log("Hide var: " + varName);
                    $('.' + varName).hide();
                } else {
                    // console.log("Show var: " + varName);
                    $('.' + varName).show();
                }
            }
        });
    }

    // When the window is resized, redraw the graph. We could have
    // been fancy here and recomputed the scales and axes and
    // transforms. But that would have required lots of effort. Let's
    // just do the simple thing here.
    var resizeTimeoutId;
    $(window).resize(function() {
        if (resizeTimeoutId) {
            clearTimeout(resizeTimeoutId);
        }
        resizeTimeoutId = setTimeout(function() {
            // Unset the timeout ID so that we'll be ready
            // for more updates.
            resizeTimeoutId = undefined;
            console.log("Time to resize the ODE graph.");

            populateOdeGraph();
        }, 400);
    });

    // ------------------------------------------------------------
    // Automata

    function populateAutomata() {
        if (!data ||
            !data.drh) {
            return;
        }

        var graphLayout =
            // Built-in, pretty good.
            // { name: 'cose',
            //   randomize: true,
            // };
            //
            // See https://github.com/cytoscape/cytoscape.js-cose-bilkent
            //
            // { name: 'cose-bilkent',
            //   randomize: true,
            //   // This is long enough to, usually, make the labels fit.
            //   idealEdgeLength: 500,
            // };
            {
                name: 'cola',
                // The infinite layout continually tries to maintain
                // positions. This makes interaction really nice. However, if
                // fit is also enabled, the result it very weird.
                infinite: true,
                fit: false,
                // Increase the space a bit to improve readability.
                edgeLength: 400,
            };

        $.each(data.drh, function(name, model) {
            var heading = $('<h2>').appendTo('#automata');
            heading.text(name);

            var graphContainer = $('<div>').appendTo('#automata');

            // var elements = [];
            var elements = getElementsForModel(model);
            if (0 === elements.length) {
                $(graphContainer).text("Model has no transitions.");
                return;
            }

            // We are going to make an actual link graph, so give the
            // graph div the right class.
            graphContainer.addClass('link-graph-container');

            // Create the graph.
            var cy = cytoscape({
                container: graphContainer,
                elements: elements,
                style: graphStyle,
                layout: graphLayout,
            });
            cy.panzoom();
        });
    }

    function getElementsForModel(model) {
        var elements = [];
        // console.log(model);
        $.each(model.modes, function(modeName, modeData) {
            var modeLabel = modeName;
            if (modeData.label) {
                modeLabel = modeData.label;
            }
            var element = {
                data: {
                    id: modeName,
                    label: modeLabel,
                }
            };
            elements.push(element);

            $.each(modeData.transitions, function(i, transition) {
                var link = {
                    data: {
                        // id: ?,
                        source: modeName,
                        target: transition.dest_mode,
                        label: transition.name,
                    }
                };
                elements.push(link);
            });
        });
        return elements;
    }

    // ------------------------------------------------------------
    // Data Manipulation

    // Constructs and returns an array of steps. Each entry in the
    // array contains an object describing the state of each
    // automaton.
    // [ { automatonId:
    //     { label: '',
    //       modeId: #,
    //       modeLabel: '',
    //     },
    //     ...
    //   } ]
    //
    function getModesByStep(modes) {
        var steps = [];
        var automata = {};

        $.each(modes, function(i, mode) {
            // Get some values, or return.
            if (!mode) {
                return;
            }
            var automatonId = mode.automaton_id;
            var automatonLabel = mode.automaton;
            var modeId = mode.mode_id;
            var modeLabel = mode.mode;
            var step = mode.step;
            if ((undefined === automatonId) ||
                !automatonLabel ||
                (undefined === modeId) ||
                !modeLabel ||
                (undefined === step)) {
                return;
            }

            if (!steps[step]) {
                steps[step] = {};
            }
            var stepObj = steps[step];

            if (!stepObj[automatonId]) {
                stepObj[automatonId] = {};
            }
            var automatonObj = stepObj[automatonId];

            automatonObj.label = automatonLabel;
            automatonObj.modeId = modeId;
            automatonObj.modeLabel = modeLabel;

            if (!automata[automatonId]) {
                automata[automatonId] = automatonLabel;
            }
        });

        // Perform some cleanup.
        verifySteps(steps, automata);
        addStateChangeIndicators(steps);

        return steps;
    }

    // Verifies that all steps are populated and include a mode for
    // each automaton.
    function verifySteps(steps, automata) {
        var numSteps = steps.length;
        for (var i = 0; i < numSteps; ++i) {
            verifyStep(i, steps, automata);
        }
    }

    function verifyStep(i, steps, automata) {
        if (!steps[i]) {
            console.warn("Step was missing entirely: " + i);
            steps[i] = {};
        }
        var step = steps[i];

        $.each(automata, function(automatonId, automatonLabel) {
            if (!step[automatonId]) {
                console.warn('Automaton (' + automatonLabel +
                             ') was missing from step ' + i);
                step[automatonId] = {
                    label: automatonLabel,
                    modeId: -1,
                    modeLabel: 'UNKNOWN',
                };
            }
        });
    }

    // Adds a stateChanged: true/false indication to each mode.
    function addStateChangeIndicators(steps) {
        var numSteps = steps.length;
        var prevStep;
        for (var i = 0; i < numSteps; ++i) {
            var step = steps[i];
            $.each(step, function(automatonId, mode) {
                var modeId = mode.modeId;
                if (!prevStep ||
                    (modeId === prevStep[automatonId].modeId)) {
                    mode.changed = false;
                } else {
                    mode.changed = true;
                }
            });

            prevStep = step;
        }
    }

    // ------------------------------------------------------------
    // Trace processing

    // Constructs and returns an array of steps. Each entry in the
    // array contains an object describing the trace of each
    // variable.
    // [ { variable:
    //     { startTime: #,
    //       endTime: #,
    //       // Later, add this...
    //       variable: [
    //         { time: [#, #],
    //           enclosure: [#, #],
    //         },
    //         ...
    //       ],
    //     },
    //     ...
    //   } ]
    //
    function getTracesByStep(traces, steps) {
        // var steps = [];

        // This stores the running time (in seconds) from trace to
        // trace. We use this to offset the times into a single
        // timeline.
        var time = 0.0;
        var sortedTraces = traces.sort(function(a, b) {
            return (a[0].step - b[0].step);
        });
        $.each(sortedTraces, function(i, trace) {
            $.each(trace, function(j, piece) {
                if (!piece) {
                    return;
                }
                var key = piece.key;
                var step = piece.step;
                var values = piece.values;
                if ((undefined === key) ||
                    (undefined === step) ||
                    (undefined === values)) {
                    console.warn("Found a bad piece:", piece);
                    return;
                }

                if (!steps[step]) {
                    steps[step] = {};
                }
                var stepObj = steps[step];

                // Get the variable from the key.
                var match = variableRegex.exec(key);
                var variable = match[1];
                if (!stepObj[variable]) {
                    stepObj[variable] = {
                        values: [],
                    };
                }
                var variableObj = stepObj[variable];

                $.each(values, function(k, val) {
                    if ((undefined === val) ||
                        (undefined === val.time)) {
                        return;
                    }
                    var startTime = time + val.time[0];
                    var endTime = time + val.time[1];
                    // Update the start/end times for the variableObj.
                    if ((undefined === variableObj.startTime) ||
                        (startTime < variableObj.startTime)) {
                        variableObj.startTime = startTime;
                    }
                    if ((undefined === variableObj.endTime) ||
                        (endTime > variableObj.endTime)) {
                        variableObj.endTime = endTime;
                    }

                    if (undefined === val.enclosure) {
                        return;
                    }

                    var varVal = {
                        time: [startTime, endTime],
                        enclosure: val.enclosure,
                    };
                    variableObj.values.push(varVal);

                    // Update the global min/max values.
                    if (val.enclosure[0] < minY) {
                        minY = val.enclosure[0];
                    }
                    if (val.enclosure[1] < minY) {
                        minY = val.enclosure[1];
                    }
                    if (val.enclosure[0] > maxY) {
                        maxY = val.enclosure[0];
                    }
                    if (val.enclosure[1] > maxY) {
                        maxY = val.enclosure[1];
                    }
                });

                // Record the start and end times for the step.
                if (undefined === stepObj.startTime) {
                    stepObj.startTime = variableObj.startTime;
                }
                if (undefined === stepObj.endTime) {
                    stepObj.endTime = variableObj.endTime;
                }

                // Verify that the start and end time for this
                // variable match the ones for the step.
                if (stepObj.startTime !== variableObj.startTime) {
                    console.warn('Variable had different start time than step.',
                                 stepObj, variableObj);
                }
                if (stepObj.endTime !== variableObj.endTime) {
                    console.warn('Variable had different end time than step.',
                                 stepObj, variableObj);
                }
            });

            // Update the time before we go on to the next step.
            if ((undefined === steps[i]) ||
                (undefined === steps[i].endTime)) {
                console.warn("Uh oh, we might have gotten steps out of order, looking for: " + i, steps[i]);
            } else {
                time = steps[i].endTime;
            }

            // Update the gloabl min/max times.
            if (time < minTime) {
                minTime = time;
            }
            if (time > maxTime) {
                maxTime = time;
            }
        });

        // FIXME Should there be a verify step here?

        return steps;
    }

    // ------------------------------------------------------------
    // Utility to come up with a new color for a timeline
    // item. Returns a style string with the background- and
    // border-color.
    //
    // Here's a site for developing a color scheme.
    // http://colorbrewer2.org/#type=qualitative&scheme=Set3&n=12

    function getTimelineColorStyle(state) {
        var hue = getHueFor(state);
        return 'background-color: ' + d3.hsl(hue, 0.5, 0.8) + ';' +
            'border-color: ' + d3.hsl(hue, 0.5, 0.6) + ';';
    }

    // Returns the base hue for this name. Assigns a new one if
    // necessary.
    function getHueFor(name) {
        var hue = hueForState[name];
        if (!hue) {
            // hue = chooseHue();
            hue = chooseGoldenRatioHue();
            hueForState[name] = hue;
        }
        return hue;
    }

    // Follows idea from this article, in the golden ratio section.
    // http://devmag.org.za/2012/07/29/how-to-choose-colours-procedurally-algorithms/
    function chooseGoldenRatioHue() {
        var offset = 60.0;

        var delta = 360.0 * (0.618033988749895 * assignedStateCount);
        var nextHue = (offset + delta) % 360.0;
        ++assignedStateCount;
        return nextHue;
    }

    function chooseHue() {
        var minHue = 200.0;
        var maxHue = 280.0;
        var cur2 = 1.0;
        var ratio;
        var nextHue;
        // console.log("hueForState", hueForState);

        while (cur2 < assignedStateCount) {
            cur2 *= 2.0;
        }
        if (0 === assignedStateCount) {
            ratio = 0;
        } else if (1 === assignedStateCount) {
            ratio = 1;
        } else if (2 === assignedStateCount) {
            ratio = 0.5;
        } else if (0 === (assignedStateCount % 2)) {
            // Even
            ratio = 1.0 - ((assignedStateCount - 1.0 - (0.5 * cur2)) / cur2);
            // console.log('even:   ' + state +
            //             '   1.0 - ((' + assignedStateCount +
            //             ' - 1.0 - ' + (0.5 * cur2) + ') / ' +
            //             cur2 + ') = ' + ratio);
        } else {
            // Odd
            ratio = (assignedStateCount - (0.5 * cur2)) / cur2;
            // console.log('odd:    ' + state +
            //             '   (' + assignedStateCount +
            //             ' - ' + (0.5 * cur2) + ') / ' +
            //             cur2 + ' = ' + ratio);
        }

        nextHue = minHue + ratio * (maxHue - minHue);
        ++assignedStateCount;

        return nextHue
    }

});
