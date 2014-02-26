gup = (name) ->
  name = name.replace(/[\[]/,"\\\[").replace(/[\]]/,"\\\]")
  regexS = "[\\?&]"+name+"=([^&#]*)"
  regex = new RegExp( regexS )
  results = regex.exec( window.location.href )
  if (results == null)
    ""
  else
    results[1]

loadScript = (url, callback) ->
  # Adding the script tag to the head as suggested before
  head = document.getElementsByTagName('head')[0]
  script = document.createElement('script')
  script.type = 'text/javascript'
  script.src = url

  # Then bind the event to the callback function.
  # There are several events for cross browser compatibility.
  script.onreadystatechange = callback
  script.onload = callback

  # Fire the loading
  head.appendChild(script)

doit = (config) ->

  vis_data_file = gup("data")
  console.log(vis_data_file)
  if (vis_data_file)
    console.log("Loaded?")
    loadScript("benchmarks/" + vis_data_file, () -> console.log("Loaded: ", config);)

  color = d3.scale.category10()
  animation_delay = config.animation_delay

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
    if (chart.id == 0)
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

    # Only collect the traces of the corresponding groups
  #  count = 0
  #  traces = _.filter(json.traces, (item) -> _.some(groups, (g) -> count = count + 1; (count % 100 == 2) && (+item[0].group) == g))
  #  traces = _.filter(json.traces, (item) -> _.some(groups, (g) -> (+item[0].group) == g))
    traces = json.traces


    # Collect data by variable and step
    result = []
    traces.forEach (trace) ->
      trace.forEach (piece) ->

        MAX_TO_SHOW=300.0
        if piece.values.length > MAX_TO_SHOW
          count = 0
          size = piece.values.length;
          divisor = Math.ceil(size / MAX_TO_SHOW);
          piece.values = _.filter(piece.values, (d) -> count = count + 1; (count % divisor == 1));

        key_strings = piece.key.split("_")
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

    # Adjust Time
    lastTime = []
    for k, trace of result
      _.each(trace, (piece) ->
        if !(k of lastTime)
          lastTime[k] = [0.0, 0.0]
        piece = addTimeToData(lastTime[k], piece)
        lastTime[k] = _.last(piece.values).time
        piece.domX = [d3.min(piece.values, (d) -> d.time[0]),
                        d3.max(piece.values, (d) -> d.time[1])]
        )
      trace.domX = [d3.min(trace, (piece) -> piece.domX[0]),
                       d3.max(trace, (piece) -> piece.domX[1])]
      trace.domY = [d3.min(trace, (piece) -> d3.min(piece.values,
                                                      (d) -> d.enclosure[0])),
                       d3.max(trace, (piece) -> d3.max(piece.values,
                                                      (d) -> d.enclosure[1]))]
    data = {}
    data.title = json.title
    data.values = _.values(result)

    data.domX = [d3.min(data.values, (trace) -> trace.domX[0]),
                 d3.max(data.values, (trace) -> trace.domX[1])]

    data.domY = [d3.min(data.values, (trace) -> trace.domY[0]),
                 d3.max(data.values, (trace) -> trace.domY[1])]

    return data

  createChart = (json) ->
    data = processJson(json)

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

    keys = data.values.length;

    chartHeight = ((height - contextHeight) / keys) - config.inter_chart_margin;

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
      (margin.top + height - contextHeight) + ")");

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
        height: chartHeight,
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

      # /* XScale is time based */
      this.xScale = d3.scale.linear()
          .range([0, this.width])
          .domain(this.chartData.domX)

      minY = d3.min(this.chartData, (p) -> p.domX[0])
      maxY = d3.max(this.chartData, (p) -> p.domX[1])

      this.yScale = d3.scale.linear()
          .range([this.height,0])
          .domain(this.chartData.domY)
      xS = this.xScale;
      yS = this.yScale;

      chart = this

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
      chartContainer = this.chartContainer =
        svg.append("g")
           .attr('class',this.name.toLowerCase())
           .attr("transform", "translate(" + this.margin.left + "," + (this.margin.top + (this.height * this.id) + (config.inter_chart_margin * this.id)) + ")");

      # MODE
      this.chartContainer.selectAll("rect")
          .data(this.chartData)
          .enter()
          .append("svg:rect")
          .on("mouseover",
            (d) ->
              d3.select(this).transition().style("fill-opacity", 0.5)
            )
          .on("mouseout",
            (d) ->
              d3.select(this).transition().style("fill-opacity", 0.2))
          .attr("x", (d) -> xS(d.domX[0]) + .5)
          .attr("y", 0)
          .attr("height", this.height)
          .attr("width", (d) -> xS(d.domX[1]) - xS(d.domX[0]) - .5)
          .attr("fill", (d) -> d3.rgb(color(d.key)).brighter(d.mode * 2))
          .style("fill-opacity", 0.0)
          .transition()
          .duration((d) -> animation_delay * (+ d.step + 1))
          .style("fill-opacity", 0.3)
          .transition()
          .duration((d) -> animation_delay / 10 * (+ d.step + 1))
          .style("fill-opacity", 0.2)
          .attr("clip-path", "url(#clip-" + this.id + ")")

      this.chartContainer.selectAll("line")
          .data(this.chartData)
          .enter()
          .append("svg:line")
          .attr("x1", (d) -> xS(d.domX[1]) + .5)
          .attr("x2", (d) -> xS(d.domX[1]) + .5)
          .attr("y1", 0)
          .attr("y2", this.height)
          .style("stroke", "#999999")
          .style("stroke-width", "0.5px")
          .attr("clip-path", "url(#clip-" + this.id + ")")

      # /* We've created everything, let's actually add it to the page */
      _.each(this.chartData, (piece) ->
        chart.chartContainer.append("path")
                            .data([piece.values])
                            .attr("class", "chart")
                            .attr("clip-path", "url(#clip-" + chart.id + ")")
                            .attr("d", chart.area)
                            .style("fill-opacity", 0.0)
                            .transition()
                            .duration(animation_delay * (+ piece.step + 1))
                            .style("fill", color(piece.key))
                            .style("fill-opacity", 0.8)
                            )

      _.each(this.chartData, (piece) ->
        chart.chartContainer.append("path")
             .data([piece.values])
             .attr("class", "line")
             .attr("clip-path", "url(#clip-" + chart.id + ")")
             .style("stroke", color(piece.key))
             .style("stroke-width", "2px")
             .style("fill-opacity", 0.0)
             .style("stroke-opacity", 0.0)
             .transition()
             .duration(animation_delay * (+ piece.step + 1))
             .style("stroke-opacity", 1.0)
             .attr("d", chart.line)
             )

      # /* We've created everything, let's actually add it to the page */

      _.each(this.chartData, (piece) ->
        data.context.append("path")
            .data([piece.values])
            .attr("class", "chart")
            .attr("d", data.contextArea)
            .style("fill", "black")
            .style("fill-opacity", 0.1)
            )

      # /* We've created everything, let's actually add it to the page */
      _.each(this.chartData, (piece) ->
        data.context.append("path")
            .data([piece.values])
            .attr("d", data.contextLine)
            .style("stroke", color(piece.key))
            .style("stroke-width", "2px")
            .style("fill-opacity", 0.0)
            )

      tickVal =_.map(data.data,
        (d)-> (d3.min(d.values, (item) -> item.time[0]) +
               d3.max(d.values, (item) -> item.time[1])) / 2)
      tickDom = [d3.min(tickVal), d3.max(tickVal)]
      tickValCard = tickDom[1] - tickDom[0]

      if(this.id == 0)
        this.xAxisTop = d3.svg.axis()
                            .scale(this.xScale)
                            .tickSize(0)
                            .tickValues(tickVal)
                            .tickFormat((n, i) -> "Mode" + data.data[i].mode)
                            .orient("bottom");

      this.xAxisBottom = d3.svg.axis().scale(this.xScale).orient("bottom");
      # /* We only want a top axis if it's the first country */
      if(this.id == 0)
        this.chartContainer.append("g")
            .attr("class", "x axis top")
            .attr("transform", "translate(0,0)")
            .call(this.xAxisTop);

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
          .attr("class","country-title")
          .attr("transform", "translate(15,40)")
          .text(this.name);

  margin = config.margin
  width = config.width - margin.left - margin.right
  height = config.height - margin.top - margin.bottom
  contextHeight = config.contextHeight
  contextWidth = width

  svg = d3.select("#chart-container").append("svg")
    .attr("width", width + margin.left + margin.right)
    .attr("height", (height + margin.top + margin.bottom));
  d3.json(config.jsonfile, createChart);

config_file=gup("config")
if(config_file)
  loadScript("benchmarks/" + config_file, () -> doit(config))
else
  doit(config)
