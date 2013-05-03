all: vis.js vis_twovar.js

vis.js: vis.coffee
	coffee -c $<

vis_twovar.js: vis_twovar.coffee
	coffee -c $<

watch: vis.coffee
	coffee -wc $<


clean:
	rm vis.js vis_twovar.js
