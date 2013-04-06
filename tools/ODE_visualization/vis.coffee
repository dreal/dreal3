color = d3.scale.category10()

showOnly = (chart, b) ->
  chart.xScale.domain(b);
  chart.chartContainer.selectAll("rect").data(chart.modes)
    .attr("x", (d) -> chart.xScale(d[0]) + .5)
    .attr("width", (d) -> chart.xScale(d[1]) - chart.xScale(d[0]) - .5)
  chart.chartContainer.selectAll("line").data(chart.modes)
    .attr("x1", (d) -> chart.xScale(d[0]) + .5)
    .attr("x2", (d) -> chart.xScale(d[0]) + .5)
  chart.chartContainer.select("path.chart").data([chart.chartData]).attr("d", chart.area);
  chart.chartContainer.select("path.line").data([chart.chartData]).attr("d", chart.line);
  chart.chartContainer.select(".x.axis.top").call(chart.xAxisTop);
  chart.chartContainer.select(".x.axis.bottom").call(chart.xAxisBottom);

addTimeToData = (t, item) ->
  item.values = item.values.map (data) ->
    ret = {}
    ret.time = [+data.time[0] + t[1], +data.time[1] + t[1]]
    ret.enclosure = data.enclosure
    return ret
  return item

processJson = (json) ->
  groups = json.groups

  # Drop the first item (which is dummy)
  json.traces = _.rest(json.traces)

  # Only collect the traces of the corresponding groups
  traces = _.filter(json.traces, (item) -> _.some(groups, (g) -> (+item[0].group) == g))

  # Collect data by variable and step
  result = []
  traces.forEach (items) ->
    items.forEach (item) ->
      key_strings = item.key.split("_")
      item.mode = _.last(key_strings)
      key_strings = _.initial(key_strings)
      s = item.step = _.last(key_strings)
      key_strings = _.initial(key_strings)
      k = item.key = key_strings.join("_")
      if !(k of result)
        result[k] = new Array()
      if !(s of result[k])
        result[k][s] = new Array()
      result[k][s] = item # Use push to collect all the items

  # Adjust Time
  lastTime = []
  for k, items of result
    _.each(items, (item) ->
      if !(k of lastTime)
        lastTime[k] = [0.0, 0.0]
      item = addTimeToData(lastTime[k], item)
      lastTime[k] = _.last(item.values).time
      item.domX = [d3.min(item.values, (p) -> p.time[0]),
                      d3.max(item.values, (p) -> p.time[1])]
      )
    items.domX = [d3.min(items, (item) -> item.domX[0]),
                     d3.max(items, (item) -> item.domX[1])]
    items.domY = [d3.min(items, (item) -> d3.min(item.values,
                                                    (p) -> p.enclosure[0])),
                     d3.max(items, (item) -> d3.max(item.values,
                                                    (p) -> p.enclosure[1]))]
  data = {}
  data.title = json.title
  data.values = _.values(result)

  data.domX = [d3.min(data.values, (k) -> k.domX[0]),
                  d3.max(data.values, (k) -> k.domX[1])]

  data.domY = [d3.min(data.values, (k) -> k.domY[0]),
                  d3.max(data.values, (k) -> k.domY[1])]

  return data

createChart = (json) ->
  data = processJson(json)

  console.log("Data:", data)

  # for k, s of data
  #     # s.modes.forEach (m) ->
  #     #   m[0] = parseFloat(m[0]);
  #     #   m[1] = parseFloat(m[1])
  #     s.values.forEach (d) ->
  #       d.time = [parseFloat(d.time[0]), parseFloat(d.time[1])];
  #       d.enclosure = [parseFloat(d.enclosure[0]), parseFloat(d.enclosure[1])]
  #     s.modes = _.zip(s.modes[...(s.modes.length-1)], s.modes[1..])
  #     data2.push(s)
  # data = data2

  charts = [];

  keys = data.length;

  chartHeight = height * (1 / keys);

  # /* Let's create the context brush that will
  #    let us zoom and pan the chart */
  contextXScale = d3.scale.linear()
      .range([0, contextWidth])
      .domain(data.domX);

  contextYScale = d3.scale.linear()
      .range([contextHeight, 0])
      .domain(data.domY);

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
    (chartHeight * keys + margin.top + margin.bottom) + ")");

  context.append("g")
    .attr("class", "x axis top")
    .attr("transform", "translate(0,0)")
    .call(contextAxis)

  _.each(data.values, (data, i) ->
    charts.push(new Chart({
      data: data,
      id: i,
      name: data.key,
      width: width,
      height: height * (1 / keys),
      domainX: data.domainX,
      svg: svg,
      margin: margin,
      context: context,
      contextArea: contextArea
      contextLine: contextLine
    })));

  context.append("text")
     .attr("class","instructions")
     .attr("transform", "translate(0," + (contextHeight + 20) + ")")
     .text('Click and drag above to zoom / pan the data');

  # /* this will return a date range to pass into the chart object */
  onBrush = () ->
    b = if brush.empty() then contextXScale.domain() else brush.extent()
    for i in [0...keys] by 1
      showOnly(charts[i], b)

  brush = d3.svg.brush()
    .x(contextXScale)
    .on("brush", onBrush);

  context.append("g")
    .attr("class", "x brush")
    .call(brush)
    .selectAll("rect")
    .attr("y", 0)
    .attr("height", contextHeight);


class Chart
  constructor: (data) ->
    this.chartData = data.data;
    this.width = data.width;
    this.height = data.height;
    this.domX = data.domX;
    this.modes = data.modes;
    this.svg = data.svg;
    this.id = data.id;
    this.name = data.name;
    this.margin = data.margin;

    console.log("ChartData: ", this.chartData)


    # /* XScale is time based */
    this.xScale = d3.scale.linear()
        .range([0, this.width])
        .domain(data.domX)

    minY = d3.min(this.chartData, (p) -> p.enclosure[0])
    maxY = d3.max(this.chartData, (p) -> p.enclosure[1])

    this.yScale = d3.scale.linear()
        .range([this.height,0])
        .domain(data.domY)
    xS = this.xScale;
    yS = this.yScale;

    # /*
    #   This is what creates the chart.
    #   There are a number of interpolation data.
    #   'basis' smooths it the most, however, when working with a lot of data, this will slow it down
    # */
    this.line = d3.svg.line()
      .interpolate("basis")
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
    this.chartContainer =
      svg.append("g")
         .attr('class',this.name.toLowerCase())
         .attr("transform", "translate(" + this.margin.left + "," + (this.margin.top + (this.height * this.id) + (20 * this.id)) + ")");



    # MODE
    this.chartContainer.selectAll("rect")
        .data(this.chartData)
        .enter()
        .append("svg:rect")
        .attr("x", (d) -> xS(d[0]) + .5)
        .attr("y", 0)
        .attr("height", this.height)
        .attr("width", (d) -> xS(d[1]) - xS(d[0]) - .5)
        .attr("fill", color(this.name))
        .style("fill-opacity", 0.1)
        .attr("clip-path", "url(#clip-" + this.id + ")")

    this.chartContainer.selectAll("line")
        .data(this.modes)
        .enter()
        .append("svg:line")
        .attr("x1", (d) -> xS(d[1]) + .5)
        .attr("x2", (d) -> xS(d[1]) + .5)
        .attr("y1", 0)
        .attr("y2", this.height)
        .style("stroke", "#999999")
        .style("stroke-width", "0.5px")
        .attr("clip-path", "url(#clip-" + this.id + ")")

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
        .attr("class", "line")
        .attr("clip-path", "url(#clip-" + this.id + ")")
        .attr("d", this.line)
        .style("stroke", color(this.name))
        .style("stroke-width", "2px")
        .style("fill-opacity", 0.0)

    # /* We've created everything, let's actually add it to the page */
    data.context.append("path")
        .data([this.chartData])
        .attr("class", "chart")
        .attr("d", data.contextArea)
        .style("fill", "black")
        .style("fill-opacity", 0.1)

    # /* We've created everything, let's actually add it to the page */
    data.context.append("path")
        .data([this.chartData])
        .attr("d", data.contextLine)
        .style("stroke", color(this.name))
        .style("stroke-width", "2px")
        .style("fill-opacity", 0.0)

    this.xAxisTop = d3.svg.axis().scale(this.xScale).orient("bottom");
    this.xAxisBottom = d3.svg.axis().scale(this.xScale).orient("bottom");
    # /* We only want a top axis if it's the first country */
    # if(this.id == 0)
    #     this.chartContainer.append("g")
    #         .attr("class", "x axis top")
    #         .attr("transform", "translate(0,0)")
    #         .call(this.xAxisTop);

    # /* Only want a bottom axis on the last country */
    this.chartContainer.append("g")
        .attr("class", "x axis bottom")
        .attr("transform", "translate(0," + this.height + ")")
        .call(this.xAxisBottom);

    this.yAxis = d3.svg.axis().scale(this.yScale).orient("left").ticks(5);

    this.chartContainer.append("g")
        .attr("class", "y axis")
        .attr("transform", "translate(0,0)")
        .call(this.yAxis);

    this.chartContainer.append("text")
        .attr("class","country-title")
        .attr("transform", "translate(15,40)")
        .text(this.name);

margin = {top: 10, right: 40, bottom: 100, left: 60}
width = 940 - margin.left - margin.right
height = 500 - margin.top - margin.bottom
contextHeight = 50
contextWidth = width

svg = d3.select("#chart-container").append("svg")
  .attr("width", width + margin.left + margin.right)
  .attr("height", (height + margin.top + margin.bottom + 200));

#d3.csv('data.csv', createChart);
d3.json('data.json', createChart);
