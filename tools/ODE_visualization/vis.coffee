color = d3.scale.category10()

createChart = (data) ->
    countries = [];
    charts = [];

    data.forEach (s) ->
        s.values.forEach (d) ->
          d.time = [parseFloat(d.time[0]), parseFloat(d.time[1])];
          d.enclosure = [parseFloat(d.enclosure[0]), parseFloat(d.enclosure[1])]

    # // /* Loop through first row and get each country
    # //    and push it into an array to use later */
    # // for (var prop in data[0]) {
    # //     if (data[0].hasOwnProperty(prop)) {
    # //         if (prop != 'Year') {
    # //             countries.push(prop);
    # //         }
    # //     }
    # // };

    keys = data.length;
    minX = d3.min(data, (d) -> d3.min(d.values, (p) -> p.time[0]))
    maxX = d3.max(data, (d) -> d3.max(d.values, (p) -> p.time[1]))
    minY = d3.min(data, (d) -> d3.min(d.values, (p) -> p.enclosure[0]))
    maxY = d3.max(data, (d) -> d3.max(d.values, (p) -> p.enclosure[1]))

    chartHeight = height * (1 / keys);

    # /* Let's create the context brush that will
    #    let us zoom and pan the chart */
    contextXScale = d3.scale.linear()
        .range([0, contextWidth])
        .domain([minX, maxX]);

    contextYScale = d3.scale.linear()
        .range([contextHeight, 0])
        .domain([minY, maxY]);

    contextAxis = d3.svg.axis()
        .scale(contextXScale)
        .tickSize(contextHeight)
        .tickPadding(-10)
        .orient("bottom");

    contextArea = d3.svg.area()
        .interpolate("monotone")
        .x0((p) -> contextXScale(p.time[0]))
        .x1((p) -> contextXScale(p.time[1]))
        .y0((p) -> contextYScale(p.enclosure[0]))
        .y1((p) -> contextYScale(p.enclosure[1]))

    contextLine = d3.svg.line()
      .interpolate("monotone")
      .x((p) -> contextXScale((p.time[0] + p.time[1]) / 2))
      .y((p) -> contextYScale((p.enclosure[0] + p.enclosure[1]) / 2))

    context = svg.append("g")
      .attr("class","context")
      .attr("transform", "translate(" + (0 + margin.left) + "," +
      (height + margin.top + chartHeight - 100) + ")");

    context.append("g")
      .attr("class", "x axis top")
      .attr("transform", "translate(0,0)")
      .call(contextAxis)

    for i in [0...keys] by 1
      charts.push(new Chart({
        data: data[i].values,
        id: i,
        name: data[i].key,
        width: width,
        height: height * (1 / keys),
        domainX: [minX, maxX],
        svg: svg,
        margin: margin,
        showBottomAxis: true
        context: context,
        contextArea: contextArea
        contextLine: contextLine
      }));

    context.append("text")
       .attr("class","instructions")
       .attr("transform", "translate(0," + (contextHeight + 20) + ")")
       .text('Click and drag above to zoom / pan the data');

    # /* this will return a date range to pass into the chart object */
    onBrush = () ->
      b = if brush.empty() then contextXScale.domain() else brush.extent()
      #for i in [0...keys] by 1
      #  charts[i].showOnly(b)

    brush = d3.svg.brush()
      .x(contextXScale)
      .on("brush", onBrush);

    context.append("g")
      .attr("class", "x brush")
      .call(brush)
      .selectAll("rect")
      .attr("y", 0)
      .attr("height", contextHeight);


Chart = (options) ->
    this.chartData = options.data;
    this.width = options.width;
    this.height = options.height;
    this.domainX = options.domainX;
    this.svg = options.svg;
    this.id = options.id;
    this.name = options.name;
    this.margin = options.margin;
    this.showBottomAxis = options.showBottomAxis;

    # /* XScale is time based */
    this.xScale = d3.scale.linear()
        .range([0, this.width])
        .domain(this.domainX)

    minY = d3.min(this.chartData, (p) -> p.enclosure[0])
    maxY = d3.max(this.chartData, (p) -> p.enclosure[1])

    this.yScale = d3.scale.linear()
        .range([this.height,0])
        .domain([minY, maxY])
    xS = this.xScale;
    yS = this.yScale;

    # /*
    #   This is what creates the chart.
    #   There are a number of interpolation options.
    #   'basis' smooths it the most, however, when working with a lot of data, this will slow it down
    # */

    this.line = d3.svg.line()
      .x((p) -> xS((p.time[0] + p.time[1]) / 2))
      .y((p) -> yS((p.enclosure[0] + p.enclosure[1]) / 2))

    this.area = d3.svg.area()
        .interpolate("basis")
        .x0((p) -> xS(p.time[0]))
        .x1((p) -> xS(p.time[1]))
        .y0((p) -> yS(p.enclosure[0]))
        .y1((p) -> yS(p.enclosure[1]))
    # /*
    #   This isn't required - it simply creates a mask. If this wasn't here,
    #   when we zoom/panned, we'd see the chart go off to the left under the y-axis
    # */
    this.svg.append("defs").append("clipPath")
        .attr("id", "clip-" + this.id)
        .append("rect")
        .attr("width", this.width)
        .attr("height", this.height);
    # /*
    #   Assign it a class so we can assign a fill color
    #   And position it on the page
    # */
    this.chartContainer = svg.append("g")
        .attr('class',this.name.toLowerCase())
        .attr("transform", "translate(" + this.margin.left + "," + (this.margin.top + (this.height * this.id) + (10 * this.id)) + ")");

    # /* We've created everything, let's actually add it to the page */
    this.chartContainer.append("path")
        .data([this.chartData])
        .attr("class", "chart")
        .attr("clip-path", "url(#clip-" + this.id + ")")
        .attr("d", this.area)
        .style("fill", color(this.name))
        .style("fill-opacity", 0.8)

    this.chartContainer.append("path")
        .data([this.chartData])
        .attr("d", this.line)
        .style("stroke", color(this.name))
        .style("stroke-width", "2px")
        .style("fill-opacity", 0.0)

    # /* We've created everything, let's actually add it to the page */
    options.context.append("path")
        .data([this.chartData])
        .attr("class", "chart")
        .attr("clip-path", "url(#clip-" + this.id + ")")
        .attr("d", options.contextArea)
        .style("fill", "black")
        .style("fill-opacity", 0.1)

    # /* We've created everything, let's actually add it to the page */
    options.context.append("path")
        .data([this.chartData])
        .attr("d", options.contextLine)
        .style("stroke", color(this.name))
        .style("stroke-width", "2px")
        .style("fill-opacity", 0.0)

    this.xAxisTop = d3.svg.axis().scale(this.xScale).orient("bottom");
    this.xAxisBottom = d3.svg.axis().scale(this.xScale).orient("top");
    # /* We only want a top axis if it's the first country */
    # if(this.id == 0)
    #     this.chartContainer.append("g")
    #         .attr("class", "x axis top")
    #         .attr("transform", "translate(0,0)")
    #         .call(this.xAxisTop);

    # /* Only want a bottom axis on the last country */
    if(this.showBottomAxis)
        this.chartContainer.append("g")
            .attr("class", "x axis bottom")
            .attr("transform", "translate(0," + this.height + ")")
            .call(this.xAxisBottom);

    this.yAxis = d3.svg.axis().scale(this.yScale).orient("left").ticks(5);

    this.chartContainer.append("g")
        .attr("class", "y axis")
        .attr("transform", "translate(-15,0)")
        .call(this.yAxis);

    this.chartContainer.append("text")
        .attr("class","country-title")
        .attr("transform", "translate(15,40)")
        .text(this.name);

Chart.prototype.showOnly = (b) ->
    this.xScale.domain(b);
    this.chartContainer.select("path").data([this.chartData]).attr("d", this.area);
    this.chartContainer.select(".x.axis.top").call(this.xAxisTop);
    this.chartContainer.select(".x.axis.bottom").call(this.xAxisBottom);

margin = {top: 10, right: 40, bottom: 100, left: 60}
width = 940 - margin.left - margin.right
height = 500 - margin.top - margin.bottom
contextHeight = 50
contextWidth = width

svg = d3.select("#chart-container").append("svg")
  .attr("width", width + margin.left + margin.right)
  .attr("height", (height + margin.top + margin.bottom));

#d3.csv('data.csv', createChart);
d3.json('data.json', createChart);
