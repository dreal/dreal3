color = d3.scale.category10()
animation_delay = 2000

showOnly = (chart, b) ->
  chart.xScale.domain(b);
  chart.chartContainer.selectAll("rect").data(chart.chartData)
    .attr("x", (d) -> chart.xScale(d.domX[0]) + .5)
    .attr("width", (d) -> chart.xScale(d.domX[1]) - chart.xScale(d.domX[0]) - .5)
  chart.chartContainer.selectAll("line").data(chart.chartData)
    .attr("x1", (d) -> chart.xScale(d.domX[0]) + .5)
    .attr("x2", (d) -> chart.xScale(d.domX[0]) + .5)

  chart.chartContainer.selectAll("path.chart").attr("d", chart.area);
  chart.chartContainer.selectAll("path.line").attr("d", chart.line);
  chart.chartContainer.select(".x.axis.top").call(chart.xAxisTop);
  chart.chartContainer.select(".x.axis.bottom").call(chart.xAxisBottom);

addTimeToData = (t, item) ->
  item.values = item.values.map (data) ->
    ret = {}
    ret.time = [+data.time[0] + t[1], +data.time[1] + t[1]]
    ret.enclosure = data.enclosure
    return ret
  return item

create_XY_data = (data, key0, key1) ->
  data_0 = data[key0]
  data_1 = data[key1]
  t1 = _.map(_.zip(data_0, data_1), (d) -> _.zip(d[0].values, d[1].values))
  t2 = _.map(t1, (piece, i) ->
    ret = _.map(piece, (d) ->
        ret = {};
        ret[key0] = d[0].enclosure;
        ret[key1] = d[1].enclosure;
        return ret
      )
      ret.mode = i
      return ret
    )
  t2.key0 = key0
  t2.key1 = key1
  return t2

processJson = (json) ->
  groups = json.groups

  # Drop the first item (which is dummy)
  json.traces = _.rest(json.traces)

  # Only collect the traces of the corresponding groups
  traces = _.filter(json.traces, (item) -> _.some(groups, (g) -> (+item[0].group) == g))

  # Collect data by variable and step
  result = []
  traces.forEach (trace) ->
    trace.forEach (piece) ->
      key_strings = piece.key.split("_")
      piece.mode = _.last(key_strings)
      key_strings = _.initial(key_strings)
      s = piece.step = _.last(key_strings)
      key_strings = _.initial(key_strings)
      k = piece.key = key_strings.join("_")
      if !(k of result)
        result[k] = new Array()
      if !(s of result[k])
        result[k][s] = new Array()
      result[k][s] = piece # Use push to collect all the trace
      result[k].key = k

  result2 = create_XY_data(result, "x", "v")

  return result2

createChart = (json) ->
  data = processJson(json)
  data.dom0 = [d3.min(data, (piece) -> d3.min(piece, (d) -> d[data.key0][0])),
               d3.max(data, (piece) -> d3.max(piece, (d) -> d[data.key0][1]))]

  data.dom1 = [d3.min(data, (piece) -> d3.min(piece, (d) -> d[data.key1][0])),
               d3.max(data, (piece) -> d3.max(piece, (d) -> d[data.key1][1]))]

  chartHeight = height;
  chart = new Chart({
      data: data,
      id: 0,
      width: width,
      height: height,
      svg: svg,
      margin: margin
    });

class Chart
  constructor: (data) ->
    this.chartData = data.data
    this.width = data.width;
    this.height = data.height;
    this.dom0 = this.chartData.dom0;
    this.svg = data.svg;
    this.id = data.id;
    this.margin = data.margin;



    # /* XScale is time based */
    this.xScale = d3.scale.linear()
        .range([0, this.width])
        .domain(this.chartData.dom0)

    this.yScale = d3.scale.linear()
        .range([this.height,0])
        .domain(this.chartData.dom1)
    xS = this.xScale;
    yS = this.yScale;

    chart = this

    # /*
    #   This is what creates the chart.
    #   There are a number of interpolation data.
    #   'basis' smooths it the most, however, when working with a lot of data, this will slow it down
    # */
    key0 = data.data.key0
    key1 = data.data.key1

    this.line = d3.svg.line()
      .interpolate("basis")
      .x((p) -> xS((p[key0][0] + p[key0][1]) / 2))
      .y((p) -> yS((p[key1][0] + p[key1][1]) / 2))

    this.area = d3.svg.area()
        .interpolate("basis")
        .x0((p) -> xS(p[key0][0]))
        .x1((p) -> xS(p[key0][1]))
        .y0((p) -> yS(p[key1][0]))
        .y1((p) -> yS(p[key1][1]))

    # /*
    #   Assign it a class so we can assign a fill color
    #   And position it on the page
    # */
    chartContainer = this.chartContainer =
      svg.append("g")
         .attr('class',data.key0 + " v.s. " + data.key1)
         .attr("transform", "translate(" + this.margin.left + "," + (this.margin.top + (this.height * this.id) + (20 * this.id)) + ")");

    # /* We've created everything, let's actually add it to the page */
    _.each(this.chartData, (piece) ->
      chart.chartContainer.append("path")
                          .data([piece])
                          .attr("class", "chart")
                          .style("fill", color(piece.mode))
                          .style("fill-opacity", 0.0)
                          .transition()
                          .duration(animation_delay * (+ piece.mode + 1))
                          .attr("d", chart.area)
                          .style("fill-opacity", 0.8)
                          )

    _.each(this.chartData, (piece) ->
      chart.chartContainer.append("path")
           .data([piece])
           .attr("class", "line")
           .style("fill-opacity", 0.0)
           .style("stroke", "white")
           .transition()
           .duration(animation_delay * (+ piece.mode + 1))
           .attr("d", chart.line)
           .style("stroke", color(piece.mode))
           .style("stroke-width", "2px")
           .style("fill-opacity", 0.0)
           )

    this.xAxisTop = d3.svg.axis().scale(this.xScale).orient("bottom");
    this.xAxisBottom = d3.svg.axis().scale(this.xScale).orient("bottom");
    # /* We only want a top axis if it's the first country */
    # if(this.id == 0)
    #     this.chartContainer.append("g")
    #         .attr("class", "x axis top")
    #         .attr("transform", "translate(0,0)")
    #         .call(this.xAxisTop);

    # /* Only want a bottom axis on the last country */
    chartContainer.append("g")
        .attr("class", "x axis bottom")
        .attr("transform", "translate(0," + this.height + ")")
        .call(this.xAxisBottom);

    this.yAxis = d3.svg.axis().scale(this.yScale).orient("left").ticks(5);

    chartContainer.append("g")
        .attr("class", "y axis")
        .attr("transform", "translate(0,0)")
        .call(this.yAxis);

    this.chartContainer.append("text")
        .attr("class","axis-label")
        .attr("transform", "translate(-15,20)")
        .text(key0);

    this.chartContainer.append("text")
        .attr("class","axis-label")
        .attr("transform", "translate(" + (+ width - 2) + ", " + (height - 3) + ")")
        .text(key1);


margin = {top: 10, right: 40, bottom: 100, left: 60}
width = 940 - margin.left - margin.right
height = 500 - margin.top - margin.bottom

svg = d3.select("#chart-container_twovar").append("svg")
  .attr("width", width + margin.left + margin.right)
  .attr("height", (height + margin.top + margin.bottom));

#d3.csv('data.csv', createChart);
d3.json('data.json', createChart);
