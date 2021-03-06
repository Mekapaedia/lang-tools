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
                    print("Reason: " + reason)

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
        self.GRAMMAR_PROPERTIES.add_deps("UNAMBIG", "NULL_UNAMBIG")
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
        for non_term in self.grammar.nonterminals:
            search_term = non_term
            chain = self.is_cyclic(search_term)
            if chain is not None and len(chain) > 1:
                chain_link = "->"
                self.GRAMMAR_PROPERTIES.invalidate("NON_CYCLIC", "Non-terminal " + non_term + " has a cyclic chain " + chain_link.join(chain))
    
    def is_cyclic(self, search_term, curr_term=None, search_chain=None):
        chain = []
        if search_term not in self.grammar.nonterminals:
            return []
        if curr_term is None:
            curr_term = search_term
        if curr_term not in self.grammar.nonterminals:
            return []
        if search_chain is None:
            search_chain = []
        search_chain.append(curr_term)
        for production in self.grammar.nonterminals[curr_term].productions:
            for symbol in production.rhs:
                ignore_symbol = False
                if symbol.name == search_term or (len(search_chain) > 0 and symbol.name in search_chain):
                    for is_terminal in production.rhs:
                        if isinstance(is_terminal, parglare.grammar.Terminal):
                            ignore_symbol = True
                    if ignore_symbol == False:
                        search_chain.append(symbol.name)       
                        return search_chain
                elif symbol.name in self.grammar.nonterminals:
                    return self.is_cyclic(search_term, curr_term=symbol.name, search_chain=search_chain)
        return chain
    
    def check_null_unambig(self):
        nullable_symbols = []
        for non_term in self.grammar.nonterminals:
            new_nullable_symbols = self.is_nullable_symbol(non_term, nullable_symbols)
            for symbol in new_nullable_symbols:
                if symbol not in nullable_symbols:
                    nullable_symbols.append(symbol)
        nullable_symbols = list(dict.fromkeys(nullable_symbols)) # remove dupes
        for nullable_symbol in nullable_symbols:
            productions = self.grammar.nonterminals[nullable_symbol].productions
            nullable_productions = []
            for production in productions:
                this_production_nullable = True
                for symbol in production.rhs:
                    if len(production.rhs) == 0:
                        this_production_nullable = True
                    elif isinstance(symbol, parglare.grammar.Terminal):
                        this_production_nullable = False
                    elif symbol.name not in nullable_symbols:
                        this_production_nullable = False
                if this_production_nullable == True:
                    nullable_productions.append(production)
            if len(nullable_productions) > 1:
                null_ambig_str = ""
                null_ambig_prod_num = len(nullable_productions)
                null_ambig_prod_prod_cnt = 0
                for nullable_production in nullable_productions: # This formatting loop is kinda ugly but it works
                    null_ambig_str += nullable_symbol
                    null_ambig_str += " -> "
                    null_ambig_str += str(nullable_production.rhs)
                    if null_ambig_prod_prod_cnt < null_ambig_prod_num - 1:
                        null_ambig_str += " and "
                    null_ambig_prod_prod_cnt += 1
                self.GRAMMAR_PROPERTIES.invalidate("NULL_UNAMBIG", "Non-terminal " + nullable_symbol + " has an ambigously nullable productions " + null_ambig_str)

    def is_nullable_symbol(self, symbol, nullable_symbols, symbol_chain=None):
        if symbol_chain is None:
            symbol_chain = [symbol]
        elif symbol in symbol_chain:
            return nullable_symbols
        else:
            symbol_chain.append(symbol)
        if symbol not in self.grammar.nonterminals or symbol in nullable_symbols:
            return nullable_symbols
        for production in self.grammar.nonterminals[symbol].productions:
            if len(production.rhs) == 0:
                if symbol not in nullable_symbols:
                    nullable_symbols.append(symbol)
                return nullable_symbols
            all_nullable = True
            for production_symbol in production.rhs:
                if production_symbol.name not in nullable_symbols:
                    new_nullable = self.is_nullable_symbol(production_symbol.name, nullable_symbols, symbol_chain=symbol_chain)
                    if production_symbol.name in new_nullable:
                        nullable_symbols.append(production_symbol.name)
                    else:
                        all_nullable = False
                    for new_nullable_symbol in new_nullable:
                        if new_nullable_symbol not in nullable_symbols:
                            nullable_symbols.append(new_nullable_symbol)
            if all_nullable == True:
                nullable_symbols.append(symbol)
        return nullable_symbols

    def check_unambig(self):
        self.GRAMMAR_PROPERTIES.invalidate("UNAMBIG", str(inspect.stack()[0][3]) + " unimplemented")
        for production in self.grammar.productions:
            if production.symbol.name == "S'":
                continue
            sentences = self.get_sentences(production.rhs)
            print(str(production) + ": " + str(sentences))
        
    def get_sentences(self, symbol_list, chain=None):
        all_term = True
        sentence = ""
        for symbol in symbol_list:
            if isinstance(symbol, parglare.grammar.Terminal):
                if symbol.name != "EMPTY":
                    sentence += symbol.name
            else:
                all_term = False
                if chain is None:
                    chain = [symbol]
                elif symbol in chain:
                    return sentence
                sentence += str(self.get_sentences([symbol], chain=chain))
        return sentence
        
        
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
