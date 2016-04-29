#!/usr/bin/env python3

import os
import signal
import re
import json
import time
from subprocess import Popen, PIPE, call


timeout = 20*60 # 20 Minute timeout
break_on_sat = False
break_on_timeout = True

class Alarm(Exception):
    pass

def alarm_handler(signum, frame):
    raise Alarm

def run_cmd(cmd, path):
	p = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE, cwd=path)
	
	proc_std = p.communicate()
	proc_ret = p.returncode

	return (proc_ret, proc_std)

def run_cmd_write_out(out_file, cmd, path):
	t = run_cmd(cmd, path)
	f = open(out_file, 'w')
	f.write(t[1][0])
	f.flush()
	f.close()
	
def run_cmd_parse_results(cmd, wpath):
	start = time.time()
	p = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE, cwd=wpath)
			
	# Set timeout signals
	signal.signal(signal.SIGALRM, alarm_handler)
	signal.alarm(timeout)
			
	proc_std = ('', '')
	proc_ret = 0
	timedout = False
			
	# Try running solving process. Kill it in case it reaches the timeout threshold.
	try:
		proc_std = p.communicate()
		proc_ret = p.returncode
		signal.alarm(0)
	except Alarm:
		p.terminate()
		timedout = True
		
	if timedout:
		return (True, '', '', '')

						
	# Get output data
	run_result_sat = len(filter(lambda x: x == 'sat', proc_std[0].splitlines())) > 0
	#run_output = [map(str.strip, s.strip().split('=')) for s in filter(lambda x: '=' in x, proc_std[0].splitlines())]
	# Get run time
	#run_time = filter(lambda x: 'Running time' in x, run_output)[0][1]
	#run_time = "%.2f" % float(re.findall("\d+.\d+", run_time)[0])
	sat_str = 'sat' if run_result_sat else 'unsat'
	out_lines = [map(str.strip, s.strip().split()) for s in proc_std[0].splitlines()]
	stats = out_lines[0]
	hybrid_nodes = stats[0]
	hybrid_conflict = stats[1]
	sat_nodes = stats[2]
	icp_nodes = stats[3]
	sat_process_time = float(stats[4])
	hybrid_solve_time = float(stats[5])
	sat_solver_time = float(stats[6])
	icp_solver_time = float(stats[7])
	#total_time = sat_process_time + hybrid_solve_time + sat_solver_time + icp_solver_time
	end = time.time()
	run_time = end - start
	run_time = "%.2f" % run_time
	return (False, sat_str, sat_nodes, run_time, hybrid_nodes, hybrid_conflict, icp_nodes, sat_process_time, hybrid_solve_time, sat_solver_time, icp_solver_time)

def preprocess_drh(path, drhfilename):
	f = open(path + '/' + drhfilename + '.drh', 'r')
	f_content = f.read()
	f.close()
	f_content_lines = f_content.splitlines()
	
	# Remove comments
	for i in range(0, len(f_content_lines)):
		line = f_content_lines[i]
		idx = str.find(line, '//')
		if idx != -1:
			line = line[0:idx]
		f_content_lines[i] = line
	
	# Recreate content without comments
	f_no_comments = ''.join((e + '\n') for e in f_content_lines)
	
	# Call cpp and pipe content as input
	p = Popen(['cpp', '-P', '-w'], stdin=PIPE, stdout=PIPE, stderr=PIPE, cwd=path)
	proc_std = p.communicate(input=f_no_comments)[0]
	proc_ret = p.returncode

	# Write output to file
	f = open(path + '/' + drhfilename + '.preprocessed.drh', 'w')
	f.write(proc_std.decode())
	f.flush()
	f.close()

# results = [(description, [((min_bound, max_bound), [(iteration, result, time, sat_nodes)])])]
def get_latex_table (results, desc):
	latex_file = ''
	latex_file += '\\begin{table}[!ht]\n\\begin{adjustwidth}{-2cm}{}\n\centering\n\\small\n\\begin{tabular}{l'
	
	for i in range(0, len(results) * 2):
		latex_file += '|c'
	
	latex_file += '}\n\\hline\n\\hline\n'
	
	latex_file += 'i'
	
	min_bound = 99
	max_bound = 0
	
	for i in range(0, len(results)):
		description = results[i][0]
		latex_file += ' & ' + description + ' & ' + description + ' (H)'
		
		for j in range(0, len(results[i][1])):
			bounds = results[i][1][j][0]
			if bounds[0] < min_bound:
				min_bound = bounds[0]
			
			if bounds[1] > max_bound:
				max_bound = bounds[1]
		
	latex_file += ' \\\\\n'
	latex_file += '\\hline\n\\hline\n'
	
	for i in range(0, len(results)):
		description = results[i][0]
	
	for j in range (min_bound, max_bound + 1):
		latex_file += str(j)
		
		for i in range(0, len(results)):
			result = results[i][1]
			
			for k in range(0, len(result)):
				sub_result = result[k]
				bounds = sub_result[0]
				sub_result_iter = sub_result[1]
				
				a_result = '-'
				
				for g in range(0, len(sub_result_iter)):
					sub_sub_result = sub_result_iter[g]
					if sub_sub_result[0] == j:
						a_result = str(sub_sub_result[2]) + ' (' + sub_sub_result[1] + ') (' + sub_sub_result[3] + ')'
						#a_result = sub_sub_result[2] + ' (' + sub_sub_result[3] + ')'
				
				latex_file += ' & ' + a_result
		latex_file += ' \\\\\n'
		
	latex_file += '\\hline\n\\hline\n'
	
	latex_file += '\\end{tabular}\n\\caption{\\small\nBenchmark results for ' + desc + '\n}\n\\label{tbl:bench}\n\\end{adjustwidth}\n\\end{table}'
	
	return latex_file

def write_latex_tables(tables, path, out):
	f = open(path + '/' + out + '.tex', 'w')
	
	#write document header
	f.write('\\documentclass{article}\n\\usepackage{graphicx}\n\\usepackage[showframe=false]{geometry}\n')
	f.write('\\usepackage{changepage}\n\\usepackage{rotating}\n')
	f.write('\\begin{document}\n\\title{dReal Benchmark Results}\n\\author{Placeholder}\n\\maketitle')
	
	f.write('\n')
	
	for i in range(0, len(tables)):
		f.write(tables[i])
		f.write('\n')
	
	f.write('\end{document}')
	f.flush()
	f.close()

if __name__ == '__main__':
	dreal2 = '/Users/danbryce/Documents/sift/silver-surfer/trunk/code/externals/dreal-git/bin/dReal'
	dreal2_bin = os.path.abspath(dreal2)
	dreal_bin = dreal2_bin
	dreal_cmd = [dreal2_bin, '--output_num_nodes', '--short_sat', '--delta_heuristic', '--delta', '--time_split_heuristic']
	
	bmc_path = '/Users/danbryce/Documents/sift/silver-surfer/trunk/code/externals/dreal-git/bin/bmc'
	bmc_bin = os.path.abspath(bmc_path)
	
	bmc_exec = [bmc_bin]
	
	results = []
		
	main_path =  os.path.dirname(os.path.abspath(__file__))
	out_path = main_path
	
	# List benchmark names (also directory name) and matching string for domain and problem instance, lower and upper instance bound
	# and instance iteration encoding.
	
	bench_info_static = [ # folder, description, column name, filename, file extension, expected result, True = network; False = singular, instances
		                 ## [ 
				        
					     ##   ("thermostat", "Thermostat Triple SAT", "Old", "thermostat-triple-sat", ".drh", "sat", False, (1, 5)),
					     ##   ("thermostat", "Thermostat Triple SAT", "New", "thermostat-triple-i-p-sat", ".py", "sat", False, (1, 5)),
					     ##   ("thermostat", "Thermostat Triple SAT", "Net", "thermostat-triple-network-sat", ".drh", "unsat", True, (1, 5))
						 ##   ],
						  ##   [
						  ##   ("thermostat", "Thermostat Triple UNSAT", "Old", "thermostat-triple", ".drh", "unsat", False, (1, 5), True),
						  ##    ("thermostat", "Thermostat Triple UNSAT", "New", "thermostat-triple-i-p", ".py", "unsat", False, (1, 5), True),
					     
					      ##   ("thermostat", "Thermostat Triple UNSAT", "Net", "thermostat-triple-network", ".drh", "sat", True, (1, 5), True)
					      ## ],
				         ##   [					        
					        ## ("thermostat", "Thermostat Double SAT", "Old", "thermostat-double-sat", ".drh", "sat", False, (1, 5)),
					        ## ("thermostat", "Thermostat Double SAT", "New", "thermostat-double-i-p-sat", ".py", "sat", False, (1, 5)),
					       ##   ("thermostat", "Thermostat Double SAT", "Net", "thermostat-double-network-sat", ".drh", "sat", True, (1, 5))
					       ## ],
						      [
						    ## ("thermostat", "Thermostat Double UNSAT", "Old", "thermostat-double", ".drh", "unsat", False, (1, 5), True),
						     ("thermostat", "Thermostat Double UNSAT", "New", "thermostat-double-i-p", ".py", "unsat", False, (1, 5), True),
						    ## 	("thermostat", "Thermostat Double UNSAT", "Net", "thermostat-double-network", ".drh", "unsat", True, (1, 5), True)							  
						    ],
						  ##  [
						  ## 	("gen", "Generator SAT", "GEN 1", "gen-1-sat", ".drh", "sat", True, (7, 7)),
						  ## 	("gen", "Generator SAT", "GEN 1", "gen-2-sat", ".drh", "sat", True, (11, 11)),
						  ## 	("gen", "Generator SAT", "GEN 1", "gen-3-sat", ".drh", "sat", True, (15, 15)),
						  ## 	("gen", "Generator SAT", "GEN 1", "gen-4-sat", ".drh", "sat", True, (19, 19)),
						  ## 	("gen", "Generator SAT", "GEN 1", "gen-5-sat", ".drh", "sat", True, (23, 23))
						  ## ],
						  ## ## [
						  ## 	("gen", "Generator UNSAT", "GEN 1", "gen-1-unsat", ".drh", "unsat", True, (1, 8)),
						  ## 	("gen", "Generator UNSAT", "GEN 1", "gen-2-unsat", ".drh", "unsat", True, (1, 16)),
						  ## 	("gen", "Generator UNSAT", "GEN 1", "gen-3-unsat", ".drh", "unsat", True, (1, 24)),
						  ## 	("gen", "Generator UNSAT", "GEN 1", "gen-4-unsat", ".drh", "unsat", True, (1, 32)),
						  ## 	("gen", "Generator UNSAT", "GEN 1", "gen-5-unsat", ".drh", "unsat", True, (1, 40))
						  ## ],
						#  [
						#	("airplane", "Airplane", "UNSAT", "airplane", ".drh", "unsat", False, (1, 5)),
						#	("airplane", "Airplane", "SAT", "airplane-sat", ".drh", "sat", False, (1, 5)),
						#	("airplane", "Airplane", "P UNSAT", "airplane-i-p", ".py", "unsat", False, (1, 5)),
						#	("airplane", "Airplane", "P SAT", "airplane-i-p-sat", ".py", "sat",False, (1, 5)),
						#	("airplane", "Airplane", "N UNSAT", "airplane-network", ".drh", "unsat", True, (1, 5)),
						#	("airplane", "Airplane", "N SAT", "airplane-network-sat", ".drh", "sat", True, (1, 5))
						#  ],
						 ##  [							
						  ## 	 ("airplane", "Airplane Single SAT", "Old", "airplane-single-sat", ".drh", "sat", False, (1, 5)),
						  ## 	 ("airplane", "Airplane Single SAT", "New", "airplane-single-i-p-sat", ".py", "sat",False, (1, 5)),
						 ##  	("airplane", "Airplane Single SAT", "Net", "airplane-single-network-sat", ".drh", "sat", True, (1, 5))
						##   ],
						      ## [
						      ## 	("airplane", "Airplane Single UNSAT", "Old", "airplane-single", ".drh", "unsat", False, (1, 5), True),
						      ## 	("airplane", "Airplane Single UNSAT", "New", "airplane-single-i-p", ".py", "unsat", False, (1, 5), True),
						      ## 	("airplane", "Airplane Single UNSAT", "Net", "airplane-single-network", ".drh", "unsat", True, (1, 5), True)
						      ## ],
						  ## [							
						  ## 	("airplane-nl", "Airplane NL Single SAT", "Old", "airplane-single-nl-sat", ".drh", "sat", False, (1, 5)),
						  ## 	("airplane-nl", "Airplane NL Single SAT", "New", "airplane-single-nl-i-p-sat", ".py", "sat", False, (1, 5)),
						  ## 	("airplane-nl", "Airplane NL Single SAT", "Net", "airplane-single-nl-network-sat", ".drh", "sat", True, (1, 5))
						  ## ],
						  ## [
						  ## 	("airplane-nl", "Airplane NL Single UNSAT", "Old", "airplane-single-nl", ".drh", "unsat", False, (1, 5), True),
						  ## 	("airplane-nl", "Airplane NL Single UNSAT", "New", "airplane-single-nl-i-p", ".py", "unsat", False, (1, 5), True),
						  ## 	("airplane-nl", "Airplane NL Single UNSAT", "Net", "airplane-single-nl-network", ".drh", "unsat", True, (1, 5), True)
						  ## ],
						   ## [
							
						   ##  	("water", "Water Double SAT", "Old", "water-double-sat", ".drh", "sat", False, (1, 5)),
						   ##  	("water", "Water Double SAT", "New", "water-double-i-p-sat", ".py", "sat", False, (1, 5)),
						   ## 	("water", "Water Double SAT", "Net", "water-double-network-sat", ".drh", "sat", True, (1, 5))
						   ## ],
						    ## [
						    ## 	("water", "Water Double UNSAT", "Old", "water-double", ".drh", "unsat", False, (1, 5), True),
						    ## 	("water", "Water Double UNSAT", "New", "water-double-i-p", ".py", "unsat", False, (1, 5), True),
						    ## 	("water", "Water Double UNSAT", "Net", "water-double-network", ".drh", "unsat", True, (1, 5), True)
						    ## ],
						  ## [
							
						  ## 	("water", "Water Triple SAT", "Old", "water-triple-sat", ".drh", "sat", False, (1, 5), True),
						  ## 	("water", "Water Triple SAT", "New", "water-triple-i-p-sat", ".py", "sat", False, (1, 5), True),
						  ## 	("water", "Water Triple SAT", "Net", "water-triple-network-sat", ".drh", "sat", True, (1, 5), True)
						  ## ],
						  ## [
						  ## 	("water", "Water Triple UNSAT", "Old", "water-triple", ".drh", "unsat", False, (1, 5), True),
						  ## 	("water", "Water Triple UNSAT", "New", "water-triple-i-p", ".py", "unsat", False, (1, 5), True),
						   ##	("water", "Water Triple UNSAT", "Net", "water-triple-network", ".drh", "unsat", True, (1, 5), True)
						##   ]
						]
						  
	
	# Check for translated directory
	merge_path = os.path.dirname(main_path)
	if not os.path.exists(merge_path):
		print('Directory: ' + merge_path + ' does not exist.')
	
	for i in range(0, len(bench_info_static)):
		bench_data = bench_info_static[i]
		results_series = []
		
		for j in range(0, len(bench_data)):
			series_info = bench_data[j]
			folder = series_info[0]
			description = series_info[1]
			sub_series_description = series_info[2]
			gen = series_info[3]
			ext = series_info[4]
			expected_result = series_info[5]
			new_format = series_info[6]
			bounds = series_info[7]
			synchronous = series_info[8]
			
			min_bound = bounds[0]
			max_bound = bounds[1]
			
			gen_file = gen + ext
			is_drh = ext == '.drh'
			
			benchmark_path = os.path.dirname(main_path + '/' + folder + '/')
			
			f = open(benchmark_path + '/' + gen + '_output.txt', 'w')
			
			normal_and_heuristic = []
			
			for z in range(0, 2):
				heuristic = True
				
				if z == 0:
					heuristic = False
					
				results_sub = []
				final_bound = 0
				
				#f.write('# Heuristic = ' + str(heuristic) + '\n')
				
				for x in range (min_bound, max_bound + 1):
					final_bound = x
					smt_file = gen + '_' + str(x) + '.smt2'
					bmc_file = gen + '_' + str(x) + '.bh'
					bench_result = ()
					
					if not is_drh:
						run_cmd_write_out(benchmark_path + '/' + smt_file, ['python', gen_file, str(x)], benchmark_path)
					else:
						preprocess_drh(benchmark_path, gen)
						
						trans_cmd = list(bmc_exec)
							
						trans_cmd.extend([gen + '.preprocessed.drh', '-k', str(x)])
						
						if new_format:
							if synchronous:
								trans_cmd.extend(['--new_format_synchronous'])
							else:
								trans_cmd.extend(['--new_format'])
							
						if heuristic:
							trans_cmd.extend(['--bmc_heuristic', bmc_file])
						
						print(trans_cmd)
						run_cmd_write_out(benchmark_path + '/' + smt_file, trans_cmd, benchmark_path)
						
					cmd_bench = list(dreal_cmd)
					
					if heuristic:
						cmd_bench.extend(['--bmc_heuristic', bmc_file])
						
					cmd_bench.extend([smt_file])
					
					print(cmd_bench)
					
					bench_result = run_cmd_parse_results(cmd_bench, benchmark_path)
						
					# write results if benchmark did not timeout
					if not bench_result[0]:
						print((x, bench_result[1], bench_result[3], bench_result[2]))
						results_sub.append((x, bench_result[1], bench_result[3], bench_result[2]))
						json.dump(bench_result, f)
						f.write('\n')
						#f.write(str(x) + ' ' bench_result + '\n')
						f.flush()
					else:
						if break_on_timeout:
							break
						
					if bench_result[1] == 'sat' and break_on_sat:
						break
				normal_and_heuristic.append(((min_bound, final_bound), results_sub))
				print(normal_and_heuristic)
			f.close()
			results_series.append((sub_series_description, normal_and_heuristic))
		write_latex_tables([get_latex_table(results_series, description)], main_path, 'series_' + description)
		#results.append(results_series)
	print(results)
