#!/usr/bin/env python3
import os
import sys
import parglare
import inspect
from collections import Counter

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
                print("Failure: " + reason)

class GrammarPropList:
    def __init__(self):
        self.prop_dict = {}
        self.prop_deps = {}

    def add_prop(self, prop):
        self.prop_dict[prop] = GrammarProperty(prop)


    # FIXME: This dependancy resolution is ugly, make it betterer
    def collect_deps(self, dep):
        dep_list = []
        if dep in self.prop_deps:
            for subdep in self.prop_deps[dep]:
                if subdep not in dep_list:
                    dep_list.append(subdep)
                additional_deps = self.collect_deps(subdep)
                for additional_dep in additional_deps:
                    if additional_dep not in dep_list:
                        dep_list.append(additional_dep)
        return dep_list
        
    def add_deps(self, prop, *deps):
        if prop not in self.prop_deps:
            self.prop_deps[prop] = []
        dep_list = []
        for dep in deps:
            if dep not in dep_list:
                dep_list.append(dep)
                additional_deps = self.collect_deps(dep)
                for additional_dep in additional_deps:
                    if additional_dep not in dep_list:
                        dep_list.append(additional_dep)
        for dep in dep_list:
            if dep not in self.prop_deps[prop]:
                self.prop_deps[prop].append(dep)
                
    def get_deps(self):
        return self.prop_deps
   
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
        self.GRAMMAR_PROPERTIES.add_prop("UNAMBIG")
        self.GRAMMAR_PROPERTIES.add_prop("IS_RECURSIVE_DECENT")
        self.GRAMMAR_PROPERTIES.add_prop("IS_REGULAR")
        self.GRAMMAR_PROPERTIES.add_prop("IS_RIGHT_REGULAR")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LEFT_REGULAR")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LL_1")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LR_0")
        self.GRAMMAR_PROPERTIES.add_prop("IS_SLR_1")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LR_1")
        self.GRAMMAR_PROPERTIES.add_prop("IS_LALR_1")
        
        self.GRAMMAR_PROPERTIES.add_deps("REALIZABLE", "REACHABLE")
        self.GRAMMAR_PROPERTIES.add_deps("IS_RECURSIVE_DECENT", "REACHABLE", "REALIZABLE", "NON_CYCLIC", "NULL_UNAMBIG", "UNAMBIG")
        self.GRAMMAR_PROPERTIES.add_deps("IS_REGULAR", "REACHABLE", "REALIZABLE", "NON_CYCLIC", "NULL_UNAMBIG", "UNAMBIG")
        self.GRAMMAR_PROPERTIES.add_deps("IS_LL_1", "REACHABLE", "REALIZABLE", "NON_CYCLIC", "NULL_UNAMBIG", "UNAMBIG")
        self.GRAMMAR_PROPERTIES.add_deps("IS_LR_0", "REACHABLE", "REALIZABLE", "NON_CYCLIC", "NULL_UNAMBIG", "UNAMBIG")
        self.GRAMMAR_PROPERTIES.add_deps("IS_LR_1", "REACHABLE", "REALIZABLE", "NON_CYCLIC", "NULL_UNAMBIG", "UNAMBIG")
        
        self.GRAMMAR_PROPERTIES.add_deps("IS_RIGHT_REGULAR", "IS_REGULAR")
        self.GRAMMAR_PROPERTIES.add_deps("IS_LEFT_REGULAR", "IS_REGULAR")
        self.GRAMMAR_PROPERTIES.add_deps("IS_SLR_1", "IS_LR_1")
        self.GRAMMAR_PROPERTIES.add_deps("IS_LALR_1", "IS_LR_1")
        
        self.CHECKED = False
        self.grammar = None
        self.check_realizable_dict = None
        self.sus_cycle = []
        if len(args) > 0:
            self.grammar = args[0]
            

    def check_reachable(self):
        reachable = []
        reachable = self.find_reachable(self.grammar.productions[0])
        reachable.append(self.grammar.nonterminals["S'"]) # S' as the start symbol is obviously reachable
        terms = self.grammar.terminals
        non_terms = self.grammar.nonterminals
        
        for term in terms.values():
            if term not in reachable:
                self.GRAMMAR_PROPERTIES.invalidate("REACHABLE", "Unreachable terminal " + str(term))
                
        for non_term in non_terms.values():
            if non_term not in reachable:
                self.GRAMMAR_PROPERTIES.invalidate("REACHABLE", "Unreachable non-terminal " + str(non_term))
        
    
    def find_reachable(self, start_production, production_chain=[]):
        reachable = []
        production_chain.append(start_production)
        for symbol in start_production.rhs:
            if symbol not in reachable:
                reachable.append(symbol)
            if isinstance(symbol, parglare.grammar.NonTerminal):
                for production in symbol.productions:
                    if production != start_production and production not in production_chain:
                        additional_reachable = self.find_reachable(production, production_chain=production_chain)
                        for additional in additional_reachable:
                            if additional not in reachable:
                                reachable.append(additional)
        return reachable
      
    def check_realizable(self):
        non_terms = self.grammar.nonterminals
        for non_term in non_terms:
            self.is_realizable(non_term)
            self.check_realizable_dict["S'"] = True
            # Assume the start symbol is realizable - as long as the chain from the start
            # symbol is (i.e: the actual start symbol defined in the grammar file), 
            # it should be, and if it isn't; it will be caught somewhere else.
            # Also, it makes the code work.
        for non_term in self.check_realizable_dict:
            if self.check_realizable_dict[non_term] == False:
                self.GRAMMAR_PROPERTIES.invalidate("REALIZABLE", "Non-terminal " + non_term + " is not realizable.")
        
    def is_realizable(self, non_term):
        if self.check_realizable_dict is None:
            self.check_realizable_dict = {}
        elif non_term in self.check_realizable_dict:
            return self.check_realizable_dict[non_term]
        self.check_realizable_dict[non_term] = False
        realizable = False
        for production in self.grammar.nonterminals[non_term].productions:
            production_realizable = True
            for symbol in production.rhs:
                if isinstance(symbol, parglare.grammar.NonTerminal):
                    symbol_realizable = self.is_realizable(symbol.name)
                    if symbol_realizable == False:
                        production_realizable = False
            if realizable == False and production_realizable == True:
                realizable = True
        if non_term in self.check_realizable_dict:
            if self.check_realizable_dict[non_term] == False and realizable == True:
                self.check_realizable_dict[non_term] = realizable
        else:
            self.check_realizable_dict[non_term] = realizable
        return realizable
            
    def check_non_cyclic(self):
        self.GRAMMAR_PROPERTIES.invalidate("NON_CYCLIC", str(inspect.stack()[0][3]) + " unimplemented")
        for non_term in self.grammar.nonterminals:
            self.sus_cycle = []
            chain = self.is_cyclic(non_term)
            print(chain)
            if len(chain) > 1:
                chain_link = "->"
                self.GRAMMAR_PROPERTIES.invalidate("NON_CYCLIC", "Non-terminal " + non_term + " has a cyclic chain " + chain_link.join(chain))
    
    def is_cyclic(self, non_term):
        tree = {non_term: {}}
        started_productions = []
        self.grammar_tree(non_term, tree=tree, started_productions=started_productions)
        chain = []    
        return chain
        
    def grammar_tree(self, non_term, tree=None, started_productions=None, root=None):
        if tree is None:
            tree = {non_term: {}}
        if root is None:
            root = tree
        print(root)
        if non_term not in started_productions:
            started_productions.append(non_term)
        if started_productions is None:
            started_productions = []
        if non_term in self.grammar.nonterminals:
            for production in self.grammar.nonterminals[non_term].productions:
                for symbol in production.rhs:
                    if symbol.name not in started_productions:
                        started_productions.append(symbol.name)
                    if non_term == symbol.name:
                        tree[non_term][symbol.name] = "Recursion"
                    elif symbol.name in self.grammar.nonterminals:
                        tree[non_term][symbol.name] = self.grammar_tree(symbol.name, tree=None, started_productions=started_productions, root=root)
                    else:
                        tree[non_term][symbol.name] = "Terminal"
        return tree
        
    
    def check_null_unambig(self):
        self.GRAMMAR_PROPERTIES.invalidate("NULL_UNAMBIG", str(inspect.stack()[0][3]) + " unimplemented")        

    def check_unambig(self):
        self.GRAMMAR_PROPERTIES.invalidate("UNAMBIG", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_recursive_decent(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_RECURSIVE_DECENT", str(inspect.stack()[0][3]) + " unimplemented")
        for production in self.grammar.productions:
            if(production.symbol.name == "S'"): # Ignore start symbol; always has a START_RULE STOP form where STOP is a terminal
                continue
            nonterms_started = False
            for symbol in production.rhs:
                if isinstance(symbol, parglare.grammar.NonTerminal):
                    nonterms_started = True
                if nonterms_started == True and isinstance(symbol, parglare.grammar.Terminal):
                    self.GRAMMAR_PROPERTIES.invalidate("IS_RECURSIVE_DECENT", production.symbol.name + ": terminal " + symbol.name + " after non-terminals.")

    def check_regular(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_REGULAR", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_right_regular(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_RIGHT_REGULAR", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_left_regular(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_LEFT_REGULAR", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_ll_1(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_LL_1", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_lr_0(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_LR_0", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_lr_1(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_LR_1", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_slr_1(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_SLR_1", str(inspect.stack()[0][3]) + " unimplemented")
        
    def check_lalr_1(self):
        self.GRAMMAR_PROPERTIES.invalidate("IS_LALR_1", str(inspect.stack()[0][3]) + " unimplemented")

    def check_grammar(self):
        if self.grammar == None:
            return
        self.check_reachable()
        self.check_realizable()
        self.check_non_cyclic()
        self.check_unambig()
        self.check_null_unambig()
        self.check_recursive_decent()
        self.check_regular()
        self.check_right_regular()
        self.check_left_regular()
        self.check_ll_1()
        self.check_lr_0()
        self.check_lr_1()
        self.check_slr_1()
        self.check_lalr_1()
                    
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
