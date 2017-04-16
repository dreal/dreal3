
flow_var = {}  
flow_dec = {}
state_dec = {} 
state_val = {}
cont_cond = {} 
jump_cond = {}

def getHdr(n):
    res = []
    for i in range(n):
        getHdr.counter += 1
        res.append(getHdr.counter)
    return res
getHdr.counter = 0

######################
# Formula generation #
######################

def print_loop(bound, steps, keys, holder):
    c = 0
    while True:
        for j in range(steps):
            hd = getHdr(holder)
            for i in keys: 
                print(cont_cond[i][j].format(c,*hd).strip())
            if c >= bound:
                return
            for i in keys:
                print(jump_cond[i][j].format(c,c+1).strip())
            c += 1

def generate(bound, steps, keys, holder, init, goal):
    print("(set-logic QF_NRA_ODE)")
    for i in keys:
        print(flow_var[i].strip())
    for i in keys:
        print(flow_dec[i].strip())
    for b in range(bound + 1):
        for i in keys:
            print(state_dec[i].format(b).strip())
    for b in range(bound + 1):
        for i in keys:
            print(state_val[i].format(b).strip())

    print(init.format(0).strip())
    print_loop(bound, steps, keys, holder)
    print(goal.format(bound).strip())
    print("(check-sat)\n(exit)")
