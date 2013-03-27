$(document).ready(function(){

    var margin = {top: 10, right: 10, bottom: 100, left: 40},
        width = 940 - margin.left - margin.right,
        height = 500 - margin.top - margin.bottom,
        contextHeight = 50;

    var svg = d3.select("body").append("svg")
        .attr("width", width + margin.left + margin.right)
        .attr("height", (height + margin.top + margin.bottom));

    var heartRateX = d3.time.scale()
        .range([0, width]);

    var heartRateY = d3.scale.linear()
        .range([height * .25,0]);

    var heartRatexAxisTop = d3.svg.axis().scale(heartRateX).tickFormat(d3.time.format("%I:%M%p")).orient("bottom"),
        heartRatexAxisBottom = d3.svg.axis().scale(heartRateX).orient("top"),
        heartRateyAxis = d3.svg.axis().scale(heartRateY).orient("left");

    var heartRateArea = d3.svg.area()
        .interpolate("basis")
        .x(function(d) { return heartRateX(d.date); })
        .y0(height * .25)
        .y1(function(d) { return heartRateY(d.values); });

    var heartrate = chartIt('heartratesdst.json','heartrates',heartRateArea, onJSON,true, false, 0,null,heartRatexAxisTop, heartRatexAxisBottom, heartRateyAxis, heartRateX, heartRateY);

    var caloriesX = d3.time.scale()
        .range([0, width]);

    var caloriesY = d3.scale.linear()
        .range([height * .25,0]);

    var caloriesxAxisTop = d3.svg.axis().scale(caloriesX).orient("bottom"),
        caloriesxAxisBottom = d3.svg.axis().scale(caloriesX).orient("top"),
        caloriesyAxis = d3.svg.axis().scale(caloriesY).orient("left");

    var caloriesArea = d3.svg.area()
        .interpolate("basis")
        .x(function(d) { return caloriesX(d.date); })
        .y0(height * .25)
        .y1(function(d) { return caloriesY(d.values); });

    var calories = chartIt('calories.json','calories',caloriesArea, onJSON,false, false, height * .25, [0,10],caloriesxAxisTop, caloriesxAxisBottom, caloriesyAxis, caloriesX, caloriesY);

    var skinX = d3.time.scale()
        .range([0, width]);

    var skinY = d3.scale.linear()
        .range([height * .25,0]);

    var skinTempxAxisTop = d3.svg.axis().scale(skinX).orient("bottom"),
        skinTempxAxisBottom = d3.svg.axis().scale(skinX).orient("top"),
        skinTempyAxis = d3.svg.axis().scale(skinY).orient("left");

    var skinTempArea = d3.svg.area()
        .interpolate("basis")
        .x(function(d) { return skinX(d.date); })
        .y0(height * .25)
        .y1(function(d) { return skinY(d.values); });

    var skinTemp = chartIt('skin-temp.json','skin-temp',skinTempArea, onJSON,false, false, height * .5, [96,104],skinTempxAxisTop, skinTempxAxisBottom, skinTempyAxis, skinX, skinY);

    var stepsX = d3.time.scale()
        .range([0, width]);

    var stepsY = d3.scale.linear()
        .range([height * .25,0]);

    var stepsxAxisTop = d3.svg.axis().scale(stepsX).orient("bottom"),
        stepsxAxisBottom = d3.svg.axis().scale(stepsX).orient("top"),
        stepsyAxis = d3.svg.axis().scale(stepsY).orient("left");

    var stepsArea = d3.svg.area()
        .interpolate("basis")
        .x(function(d) { return stepsX(d.date); })
        .y0(height * .25)
        .y1(function(d) { return stepsY(d.values); });

    var steps = chartIt('steps.json','steps',stepsArea, onJSON,false, true,height * .75, [0,170],stepsxAxisTop, stepsxAxisBottom, stepsyAxis, stepsX, stepsY);

    function chartIt(file,v,area,callback, ticksTop, ticksBottom, mar, vr, xAxisTop, xAxisBottom, yAxis, x, y){

        svg.append("defs").append("clipPath")
            .attr("id", v + "-clip")
            .append("rect")
            .attr("width", width)
            .attr("height", height * .25);

        var focus = svg.append("g")
            .attr('class',v)
            .attr("transform", "translate(" + margin.left + "," + (margin.top + mar + 50) + ")");

        d3.json(file, function(data) {
            var chart = data[v];

            chart.forEach(function(d, i) {
                td = new XDate(+d[0])
                //d.date = td.setMonth(2).setDate(11).getTime();
                d.date = td.setMonth(10).setDate(4).getTime();
                d.values = d[1];
            });

            x.domain(d3.extent(chart.map(function(d) { return d.date; })));

            if(vr){
                // Vertical range - 0 to 150
                //y.domain([0,150]);
                y.domain(vr);
            }else{
                y.domain(d3.extent(chart.map(function(d) { return d.values; })));
            }

            focus.append("path")
                .data([chart])
                .attr("class", "chart")
                .attr("clip-path", "url(#" + v + "-clip)")
                .attr("d", area);

            if(ticksTop){
                focus.append("g")
                    .attr("class", "x axis top")
                    .attr("transform", "translate(0,0)")
                    .call(xAxisTop);
            }

            if(ticksBottom){
                focus.append("g")
                    .attr("class", "x axis bottom")
                    .attr("transform", "translate(0," + (height * .25) + ")")
                    .call(xAxisBottom);
            }

            focus.append("g")
                .attr("class", "y axis")
                .call(yAxis);

            callback();
        });

        return focus;
    }

    var jsonCount = 0;
    function onJSON(){
        jsonCount++;

        //if(jsonCount > 3){
        setupContext();
        //}
    }

    var brush, x2, y2;

    function setupContext(){
        x2 = d3.time.scale()
            .range([0, width]);

        y2 = d3.scale.linear()
            .range([contextHeight, 0]);

        x2.domain(heartRateX.domain());
        y2.domain(heartRateY.domain());

        var contextArea = d3.svg.area()
            .interpolate("monotone")
            .x(function(d) { return x2(d.date); })
            .y0(contextHeight)
            .y1(function(d) { return y2(d.heartrate); });

        brush = d3.svg.brush()
            .x(x2)
            .on("brush", onBrush);

        var context = svg.append("g")
            .attr("class","context")
            .attr("transform", "translate(" + 40 + "," + 0 + ")");

        context.append("g")
            .attr("class", "x brush")
            .call(brush)
            .selectAll("rect")
            .attr("y", -6)
            .attr("height", contextHeight);
    }

    function onBrush() {

        heartRateX.domain(brush.empty() ? x2.domain() : brush.extent());

        heartrate.select("path").attr("d", heartRateArea);
        heartrate.select(".x.axis.top").call(heartRatexAxisTop);
        heartrate.select(".x.axis.bottom").call(heartRatexAxisBottom);

        caloriesX.domain(brush.empty() ? x2.domain() : brush.extent());

        calories.select("path").attr("d", caloriesArea);
        calories.select(".x.axis.top").call(caloriesxAxisTop);
        calories.select(".x.axis.bottom").call(caloriesxAxisBottom);

        skinX.domain(brush.empty() ? x2.domain() : brush.extent());

        skinTemp.select("path").attr("d", skinTempArea);
        skinTemp.select(".x.axis.top").call(skinTempxAxisTop);
        skinTemp.select(".x.axis.bottom").call(skinTempxAxisBottom);

        stepsX.domain(brush.empty() ? x2.domain() : brush.extent());

        steps.select("path").attr("d", stepsArea);
        steps.select(".x.axis.top").call(stepsxAxisTop);
        steps.select(".x.axis.bottom").call(stepsxAxisBottom);

    }
});
