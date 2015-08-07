#!/usr/bin/env python3

import os
import signal
from subprocess import Popen, PIPE

class Alarm(Exception):
    pass

def alarm_handler(signum, frame):
    raise Alarm

if __name__ == '__main__':
	timeout = 10*60 # 10 Minute timeout
	heuristic = True
	dreach = '/home/alex/Documents/actual/dreal3/bin/dReach'
	dreach_bin = os.path.abspath(dreach)
	dreach_exec = [dreach_bin, '-n']
	max_boundary = 20
	min_boundary = 0
	
	if not heuristic:
		dreach_exec.extend(['-d'])
	else:
		dreach_exec.extend(['-b'])
		
	main_path =  os.path.dirname(os.path.abspath(__file__))
	out_path = main_path
	
	# List benchmark names (also directory name) and matching string for domain and problem instance, lower and upper instance bound
	# and instance iteration encoding.
	bench_info = {	'gen': ('gen-<i>-sat.drh', (1, 5), "%d"),
					'gen': ('gen-<i>-unsat.drh', (1, 5), "%d")
				}
					
	
	# Check for translated directory
	merge_path = os.path.dirname(main_path)
	if not os.path.exists(merge_path):
		print('Directory: ' + merge_path + ' does not exist.')
	
	# Benchmark files
	for key in bench_info:
		bench_data = bench_info[key]
		
		domain = bench_data[0]
		bounds = bench_data[1]
		encode = bench_data[2]
		
		lower_bound = bounds[0]
		upper_bound = bounds[1]
		
		benchmark_path = os.path.dirname(main_path + '/' + key + '/')
		
		if not os.path.exists(benchmark_path):
			print('Directory: ' + benchmark_path + ' does not exist.')
			continue
		
		result_file_path = os.path.abspath(benchmark_path + '/results.txt')
		result_file = open(result_file_path, 'w+')
		
		# Run mcta for all instances
		for i in range(lower_bound, upper_bound + 1):
			instance_num = encode% i
			
			domain_inst = domain.replace('<i>', instance_num)
			domain_inst_path = os.path.abspath(benchmark_path + '/' + domain_inst)
			
			if not os.path.exists(domain_inst_path):
				print('Problem file: ' + domain_inst_path + ' does not exist.')
				continue
			
			for j in range (min_boundary, max_boundary + 1):
				benchmark_exec = list(dreach_exec)
				benchmark_exec.extend(['-l', str(j), '-k', str(j), domain_inst, '--stat'])
				print('Running: ' + domain_inst_path)
				p = Popen(benchmark_exec, stdin=PIPE, stdout=PIPE, stderr=PIPE, cwd=benchmark_path)
			
				# Set timeout signals
				signal.signal(signal.SIGALRM, alarm_handler)
				signal.alarm(timeout)
			
				proc_std = ('', '')
				proc_ret = 0
			
				# Try running solving process. Kill it in case it reaches the timeout threshold.
				try:
					proc_std = p.communicate()
					proc_ret = p.returncode
					signal.alarm(0)
				except Alarm:
					res_str = 'Benchmark for: ' + domain_inst_path + ' timed out after ' + str(timeout) + ' seconds.'
					print(res_str)
					result_file.write(res_str + '\n')
				
				result_file.write('Output for: ' + domain_inst_path + '\n')
				result_file.write(proc_std[0])
				result_file.flush()
		result_file.close()