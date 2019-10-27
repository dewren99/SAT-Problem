#!/usr/bin/python3
# CMPT310 A2
#####################################################
#####################################################
# Please enter the number of hours you spent on this
# assignment here
"""
num_hours_i_spent_on_this_assignment = 
"""
#
#####################################################
#####################################################

#####################################################
#####################################################
# Give one short piece of feedback about the course so far. What
# have you found most interesting? Is there a topic that you had trouble
# understanding? Are there any changes that could improve the value of the
# course to you? (We will anonymize these before reading them.)
"""
<Your feedback goes here>


"""
#####################################################
#####################################################
import sys, getopt
import copy
import random
import time
import numpy as np
sys.setrecursionlimit(10000)

class SatInstance:
    def __init__(self):
        pass

    def from_file(self, inputfile):
        self.clauses = list()
        self.VARS = set()
        self.p = 0
        self.cnf = 0
        with open(inputfile, "r") as input_file:
            self.clauses.append(list())
            maxvar = 0
            for line in input_file:
                tokens = line.split()
                if len(tokens) != 0 and tokens[0] not in ("p", "c"):
                    for tok in tokens:
                        lit = int(tok)
                        maxvar = max(maxvar, abs(lit))
                        if lit == 0:
                            self.clauses.append(list())
                        else:
                            self.clauses[-1].append(lit)
                if tokens[0] == "p":
                    self.p = int(tokens[2])
                    self.cnf = int(tokens[3])
            assert len(self.clauses[-1]) == 0
            self.clauses.pop()
            if (maxvar > self.p):
                print("Non-standard CNF encoding!")
                sys.exit(5)
        # Variables are numbered from 1 to p
        for i in range(1, self.p + 1):
            self.VARS.add(i)

    def __str__(self):
        s = ""
        for clause in self.clauses:
            s += str(clause)
            s += "\n"
        return s


def main(argv):
    inputfile = ''
    verbosity = False
    inputflag = False
    try:
        opts, args = getopt.getopt(argv, "hi:v", ["ifile="])
    except getopt.GetoptError:
        print('DPLLsat.py -i <inputCNFfile> [-v] ')
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print('DPLLsat.py -i <inputCNFfile> [-v]')
            sys.exit()
        ##-v sets the verbosity of informational output
        ## (set to true for output veriable assignments, defaults to false)
        elif opt == '-v':
            verbosity = True
        elif opt in ("-i", "--ifile"):
            inputfile = arg
            inputflag = True
    if inputflag:
        instance = SatInstance()
        instance.from_file(inputfile)
        #start_time = time.time()
        solve_dpll(instance, verbosity)
        #print("--- %s seconds ---" % (time.time() - start_time))

    else:
        print("You must have an input file!")
        print('DPLLsat.py -i <inputCNFfile> [-v]')


# Finds a satisfying assignment to a SAT instance,
# using the DPLL algorithm.
# Input: a SAT instance and verbosity flag
# Output: print "UNSAT" or
#    "SAT"
#    list of true literals (if verbosity == True)
#
#  You will need to define your own
#  DPLLsat(), DPLL(), pure-elim(), propagate-units(), and
#  any other auxiliary functions
def solve_dpll(instance, verbosity):
    # print(instance)
    # # instance.VARS goes 1 to N in a dict
    # print(instance.VARS)
    # print(verbosity)
    ###########################################
    # Start your code
    clauses = copy.deepcopy(instance.clauses)
    clausess = copy.deepcopy(instance.clauses)
    variables = copy.deepcopy(instance.VARS)

    symbols = copy.deepcopy(variables)
    model = {}

    def DPLLsat(clauses, symbols, model):
        # if len(clauses) == 0:
        #     return model

        # if clausesNotValid(clauses):
        #     return False

        # clauses = pure_elim(clauses,symbols, model)
        # alpha = unitProp(clauses)
        # # print("ALPHA: ", alpha)
        # if alpha == False:
        #     return False
        # if len(alpha) == 0:
        #     return model

        # P = symbols.pop()
        # for value in [0,1]:

        for i in range(len(symbols)):
            for j in range(len(symbols)):
                model.update({j+1:i%2})
                clauses = pure_elim(clauses,symbols, model)
                alpha = unitProp(clauses)
                alpha = simplify(clauses, model)
                ret, truth = alpha
                if truth is not False:
                    return model
        return False

        # model.update({P:1})
        # alpha = simplify(clauses, model)
        # print("alpha: ", alpha)
        # ret = DPLLsat(clauses, symbols, model)
        # if ret is not False:
        #     return ret
        # return DPLLsat(clauses, variables, model)
    

    def unitProp(clauses):
        # print("HELLO")
        if clausesNotValid(clauses):
            return False
        l = [clause[0] for clause in clauses if len(clause)==1]
        if len(l) == 0:
            return clauses
        # print("Begining L: ", l)
        while len(l) != 0:
            # print("L: ", l)
            for literal in l: 
                for clause in reversed(clauses):
                    if len(clause) == 0:
                        return False
                    if len(clause) != 1 and literal in clause:
                        clauses.remove(clause)
                    if len(clause) != 1 and -literal in clause:
                        clause.remove(-literal)
            old_l = l
            l = [clause[0] for clause in clauses if len(clause)==1]
            if l == old_l:
                l = []
        return clauses, True

    def pure_elim(clauses, symbols, model):
        pos = [var for clause in clauses for var in clause if var > 0]
        pos = list(dict.fromkeys(pos))
        neg = [var for clause in clauses for var in clause if var < 0]
        neg = list(dict.fromkeys(neg))
        vars = []
        for x in neg:
            if abs(x) not in pos:
                vars.append(x)
        for x in pos:
            if -x not in neg:
                vars.append(x)
        for symbol in vars:
            if symbol > 0: model.update({symbol:1})
            if symbol < 0: model.update({-symbol:0})
            for clause in reversed(clauses):
                if symbol in clause:
                    clauses.remove(clause)
        return clauses


    def simplify(clauses, model):
        # print("B4: ", clauses)
        # print("Model: ",model)
        simplifiedClauses = copy.deepcopy(clauses)
        for literal, truthValue in model.items():
            for clause in reversed(simplifiedClauses):
                # print("clause for +: ", clause)
                if literal in clause:
                    if truthValue == 1: simplifiedClauses.remove(clause)
                    if truthValue == 0: clause.remove(literal)
            for clause in reversed(simplifiedClauses):
                if -literal in clause:
                    if truthValue == 1: clause.remove(-literal)
                    if truthValue == 0: simplifiedClauses.remove(clause)
        # print("SIMPLIFIED: ", simplifiedClauses)
        if len(simplifiedClauses) == 0:
            return (simplifiedClauses, True)
        return (simplifiedClauses, False)

    def clausesNotValid(clauses):
        if any(len(clause) == 0 for clause in clauses):
            return True
        else:
            return False

    callF = DPLLsat(clauses, variables, model)
    # callF = DPLL(clauses, variables, model)
    # print("CallF: ", callF)

    if callF is None:
        print("Returned NULL")
    if callF is False:
        print("UNSAT")
    if verbosity is True and callF is not False and callF is not None:
        output = []
        for symbol, truthValue in callF.items():
            if truthValue == 1:
                output.append(symbol)
        print("SAT")
        output.sort()
        print(output)
        
    if verbosity is False and callF is not False and callF is not None:
        print("SAT")

    # if verbosity is False and callF is False:
    #     print("UNSAT")
    ###########################################

if __name__ == "__main__":
    main(sys.argv[1:])
