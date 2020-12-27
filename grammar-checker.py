#!/usr/bin/env python3
import os
import sys
import parglare

class GrammarProperty:
    def __init__(self, name):
        self.name = name
        self.valid = True
        self.invalid_reasons = []
    def invalidate(self):
        self.valid = False
    def isvalid(self):
        return self.valid
    def add_reason(self, reason):
        self.invalid_reasons.append(reason)
    def print_info(self):
        print(self.name + ": " + str(self.valid))
        if(self.valid == False):
            for reason in self.invalid_reasons:
                print(reason)

class GrammarPropList:
    def __init__(self):
        self.prop_dict = {}
        self.prop_deps = {}
    def add_prop(self, prop):
        self.prop_dict[prop] = GrammarProperty(prop)
    def add_deps(self, prop, *deps):
        if prop not in self.prop_deps:
            self.prop_deps[prop] = []
        for dep in deps:
            self.prop_deps[prop].append(dep)
    def invalidate(self, prop, reason):
        self.prop_dict[prop].invalidate()
        self.prop_dict[prop].add_reason(reason)
        for deps in self.prop_deps.items():
            if(prop in deps[1]):
                self.prop_dict[deps[0]].invalidate()
                self.prop_dict[deps[0]].add_reason("Dependancy " + prop + " failed, reason: " + reason)
    def print_info(self):
        for prop in self.prop_dict.values():
            prop.print_info()

class GrammarChecker:
    def __init__(self, *args):
        self.GRAMMAR_PROPERTIES = GrammarPropList()
        self.GRAMMAR_PROPERTIES.add_prop("REACHABLE")
        self.GRAMMAR_PROPERTIES.add_prop("REALIZABLE")
        self.GRAMMAR_PROPERTIES.add_prop("NON_CYCLIC")
        self.GRAMMAR_PROPERTIES.add_prop("NULL_UNAMBIG")
        self.GRAMMAR_PROPERTIES.add_prop("IS_RECURSIVE_DECENT")
        self.GRAMMAR_PROPERTIES.add_prop("IS_REGULAR")
        self.GRAMMAR_PROPERTIES.add_prop("IS_RIGHT_REGULAR")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LEFT_REGULAR")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LL_1")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LR_0")
        self.GRAMMAR_PROPERTIES.add_prop("IS_SLR_1")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LR_1")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LALR_1")
        
        self.GRAMMAR_PROPERTIES.add_deps("IS_RIGHT_REGULAR", "IS_REGULAR")
        self.GRAMMAR_PROPERTIES.add_deps("IS_LEFT_REGULAR", "IS_REGULAR")
        
        self.CHECKED = False
        self.grammar = None
        if len(args) > 0:
            self.grammar = args[0]

    def check_grammar(self):
        for production in self.grammar.productions:
            if(production.symbol.name == "S'"):
                continue
            nonterms_started = False
            num_nonterms = 0
            for symbol in production.rhs:
                if isinstance(symbol, parglare.grammar.NonTerminal):
                    nonterms_started = True
                    num_nonterms = num_nonterms + 1
                    if(num_nonterms > 1):
                        self.GRAMMAR_PROPERTIES.invalidate("IS_REGULAR", "More than one rhs non-terminal in production " + production.symbol.name)
                if nonterms_started == True and isinstance(symbol, parglare.grammar.Terminal):
                    self.GRAMMAR_PROPERTIES.invalidate("IS_RECURSIVE_DECENT", production.symbol.name + ": terminal " + symbol.name + " after non-terminals.")
                    self.GRAMMAR_PROPERTIES.invalidate("IS_RIGHT_REGULAR", production.symbol.name + ": terminal " + symbol.name + " after non-terminals.")
                    
        self.CHECKED = True
    
    def print_properties(self):
        if(self.CHECKED == False):
            print("Grammar has yet to be checked.")
        else:
            self.GRAMMAR_PROPERTIES.print_info()
    

if __name__ == "__main__":
    if(len(sys.argv) < 2):
        print("A file argument is required")
        exit(1)
    grammar = parglare.Grammar.from_file(sys.argv[1])
    checker = GrammarChecker(grammar)
    checker.check_grammar()
    checker.print_properties()
