# %%
'''

EXPLANATION ON HOW TO INSERT FORMULAS CORRECTLY IN THE BELIEFSET

All the variables should be lowercase letters from the alphabet except for 'v' (v is used for 'or' operations)

If the formula is something simple, like 'p', '¬q', 'p -> q',..., then no parenthesis are needed.
This simple formulas are: (please make sure the spaces are written correctly)
1. Proposition: 'p'
2. Negation: '¬p'
3. Implication: 'p -> q', '¬p -> q', 'p -> ¬q', '¬p -> ¬q'
4. Disjunction: 'p v q'
5. Conjuntion: 'p ^ q'
6. If and only if: 'p <-> q'

If more complex formulas are written, then parenthesis are needed.
This more complex formulas are: (note that x and y can be any of the simple formulas)
7. Complex negation: '¬(x)'
8. Complex implication: '(x) -> (y)'
9. Complex disjunction: '(x) v (y)'
10. Complex conjuntion: '(x) ^ (y)'
11. Complex if and only if: '(x) <-> (y)'

'''


####################################################################################

import re
import itertools

####################################################################################

# Regular expressions for different patterns
# Proposition
pattern_proposition = r'^[a-z]$'
# Negation
pattern_negation = r'^¬*[a-z]$'
# Implication (4 different patterns)
pattern_imp_1_1 = r'^([a-z]) (->) ([a-z])$'
pattern_imp_1_2 = r'^(¬[a-z]) (->) ([a-z])$'
pattern_imp_1_3 = r'^([a-z]) (->) (¬[a-z])$'
pattern_imp_1_4 = r'^(¬[a-z]) (->) (¬[a-z])$'
# Or, And & If and only if
pattern_or = r'^([a-z]) (v) ([a-z])$'
pattern_and = r'^([a-z]) (\^) ([a-z])$'
pattern_iff = r'^([a-z]) (<->) ([a-z])$'
# Same as before but with recursion (for formulas like (p -> q) -> (q ^ r) )
pattern_negation2 = r'^(¬)\((.*)\)'
pattern_imp2 = r'^(?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\) (->) (?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\)$'
pattern_or2 = r'^(?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\) (v) (?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\)$'
pattern_and2 = r'^(?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\) (\^) (?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\)$'
pattern_iff2 = r'^(?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\) (<->) (?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\)$'
# Expressions for all the operators
pattern_binary_operators = r'^([a-z]) (->|v|\^|<->) ([a-z])$'
pattern_with_parenthesis = r'^(?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\) (->|v|\^|<->) (?=(?:[^()]*\([^()]*\))*[^()]*$)\((.*)\)$'

####################################################################################

class BeliefSet():
    def __init__(self):
        # Initialize belief set as an empty list
        self.beliefset = []

    # Expand the beliefset by inserting a proposition at a specified priority
    def expansion(self, beliefset, proposition, priority):
        if proposition not in beliefset:
            if self.is_well_defined(proposition):  # Checks if the proposition is well defined
                beliefset.insert(priority, proposition)
                self.beliefset, _ = self.check_beliefset(beliefset)  # Checks if the beliefset is consistent with the new proposition inside
                return self.beliefset
            else:
                raise ValueError('This formula is not written correctly')
        else:
            return self.beliefset
                
    # Contract the belief set by removing a proposition if it exists
    def contraction(self, beliefset, proposition):
        if proposition in beliefset:
            beliefset.remove(proposition)
        return beliefset
    
    # Revise the belief set with a new proposition at a specified priority
    def revision(self, beliefset, proposition, priority):
        if proposition[0] == '¬': # If it's ¬p, then ¬(¬p) = p
            proposition2 = proposition[1:]
        else:
            proposition2 = '¬' + proposition
        if self.is_well_defined(proposition):
            if proposition2 in beliefset:
                beliefset = self.contraction(beliefset, proposition2)
            self.beliefset = self.expansion(beliefset, proposition, priority)
        return self.beliefset

    # AGM Postulates
    def contraction_success(self, belset, prop):
        new_contraction = self.contraction(belset, prop)
        return None if prop not in new_contraction else ValueError('Error in AGM Contraction - Success')

    def contraction_inclusion(self, belset, prop):
        new_contraction = self.contraction(belset,prop)
        for bel in new_contraction: 
            if bel not in belset:
                return ValueError('Error in AGM Contraction - Inclusion')
    
    def contraction_vacuity(self, belset, prop):
        new_contraction = self.contraction(belset, prop)
        _, true_false = self.check_beliefset(belset)
        if not self.check2([prop], true_false):
            return None if belset == new_contraction else ValueError('Error in AGM Contraction - Vacuity')
    
    def contraction_extensionality(self, belset, prop1, prop2):
        iff = prop1 + ' <-> ' + prop2
        if re.match(pattern_iff2, iff) and iff in belset: 
            return None if self.contraction(belset, prop1) == self.contraction(belset, prop2) else ValueError('Error in AGM Contraction - Extensionality')
    
    def revision_success(self, belset, prop):
        new_revision = self.revision(belset, prop, 0)
        return None if prop in new_revision else ValueError('Error in AGM Revision - Success')
    
    def revision_inclusion(self, belset1, prop):
        return None if all(x in  self.expansion(belset1, prop,0) for x in self.revision(belset1, prop, 0)) else ValueError('Error in AGM Revision - Inclusion')

    def revision_vacuity(self, belset, prop):
        if '¬' + prop not in belset:
            return None if self.revision(belset, prop, 0) == self.expansion(belset, prop,0) else ValueError('Error in AGM Revision - Vacuity')

    def revision_consistency(self, belset, prop):
        b_add, _ = self.check_beliefset(belset)
        if not b_add == []:
            bb_add, _ = self.check_beliefset(self.revision(belset, prop, 0))
            return None if prop in bb_add else ValueError('Error in AGM Revision - Consistency')

    def revision_extensionality(self, belset, prop1, prop2):
        iff = prop1 + ' <-> ' + prop2
        if re.match(pattern_iff2, iff) and iff in belset: 
            return None if self.contraction(belset, prop1) == self.contraction(belset, prop2) else ValueError('Error in AGM Revision - Extensionality')


    # This is an auxiliar function that, given a single beliefset and a dict (like beliefset = 'q' & dic1 = [p:False, q:True, R:True]),
    # checks if beliefset can be satisfied with the values in dic1 (in that case, beliefset can be satisfies with q:True so it will return True)
    def check2(self, beliefset, dic1):
        _ , dict = self.check_beliefset(beliefset)
        dict = dict[0]
        for d in dict:
            for d_d in dic1:
                if dict[d] != d_d[d]:
                    return False
        return True
            
    
    # Check if the given formula is well defined
    def is_well_defined(self, formula):
        if re.match(pattern_proposition, formula) or re.match(pattern_negation, formula) or re.match(pattern_imp_1_1, formula) or re.match(pattern_imp_1_2, formula) or re.match(pattern_imp_1_3, formula) or re.match(pattern_imp_1_4, formula) :   # If the formula is a basic proposition or negation
            return True
        elif re.match(pattern_with_parenthesis, formula):  # If the formula is like (p -> q) ^ (q v r) 
            match = re.match(pattern_with_parenthesis, formula)
            left_operand = match.group(1)
            right_operand = match.group(3)
            return self.is_well_defined(left_operand) and self.is_well_defined(right_operand)
        elif re.match(pattern_binary_operators, formula):  # If the formula is like p -> q
            match = re.match(pattern_binary_operators, formula)
            left_operand = match.group(1)
            right_operand = match.group(3)
            return self.is_well_defined(left_operand) and self.is_well_defined(right_operand)
        else:
            return False
    
    # Clear the belief set
    def empty(self):
        self.beliefset = []

    # Return the current belief set
    def returnset(self):
        return self.beliefset

    # Get the truth value of a formula (elem) based on a truth assignment (n_dic)
    # This formula is only used in the function check_beliefset
    def get(self, elem, n_dic):
        dic = n_dic.copy()

        # Check simple propositions and negations
        if re.match(pattern_proposition, elem):
            if dic[elem] == True:
                return True
            else: 
                return False
        elif re.match(pattern_negation, elem):
            if dic[elem[1]] == False:
                return True
            else:
                return False

        # Check implication (all of them)
        elif re.match(pattern_imp_1_1, elem):
            match = re.match(pattern_imp_1_1, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left] == True and dic[right] == False :
                return False
            else:
                return True
        elif re.match(pattern_imp_1_2, elem):
            match = re.match(pattern_imp_1_2, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left[1]] == False and dic[right] == False :
                return False
            else:
                return True
        elif re.match(pattern_imp_1_3, elem):
            match = re.match(pattern_imp_1_3, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left] == True and dic[right[1]] == True :
                return False
            else:
                return True
        elif re.match(pattern_imp_1_4, elem):
            match = re.match(pattern_imp_1_4, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left[1]] == False and dic[right[1]] == True :
                return False
            else:
                return True
            
        # Handle disjunctions
        elif re.match(pattern_or, elem):
            match = re.match(pattern_or, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left] == False and dic[right] == False: 
                return False
            else:
                return True
        # Handle conjunctions
        elif re.match(pattern_and, elem):
            match = re.match(pattern_and, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left] == False or dic[right] == False:  
                return False
            else: 
                return True
        # Handle biconditionals
        elif re.match(pattern_iff, elem):
            match = re.match(pattern_iff, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            if dic[left] != dic[right]: 
                return False
            else:
                return True
            
        # Handle more complex negated formulas
        elif re.match(pattern_negation2, elem):
            match = re.match(pattern_negation2, elem)
            _, form = match.group(1), match.group(2)
            f1 = self.get(form, dic)
            if f1 == True:
                return False
            else: 
                return  True
            
        # Handle more complex implications
        elif re.match(pattern_imp2, elem):
            match = re.match(pattern_imp2, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            f1 = self.get(left, dic)
            f2 = self.get(right, dic)
            if f1 == True and f2 == False:
                return False
            else:
                return True
        # Handle more complex disjunctions
        elif re.match(pattern_or2, elem):
            match = re.match(pattern_or2, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            f1 = self.get(left, dic)
            f2 = self.get(right, dic)
            if f1 == False and f2 == False:
                return False
            else:
                return True
        # Handle more complex conjunctions
        elif re.match(pattern_and2, elem):
            match = re.match(pattern_and2, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            f1 = self.get(left, dic)
            f2 = self.get(right, dic)
            if f1 == False or f2 == False:
                return False
            else:
                return True
        # Handle more complex biconditionals
        elif re.match(pattern_iff2, elem):
            match = re.match(pattern_iff2, elem)
            left, _, right = match.group(1), match.group(2), match.group(3)
            f1 = self.get(left, dic)
            f2 = self.get(right, dic)
            if f1 != f2:
                return False
            else:
                return True

        return True

    # See if the beliefset is consistent and if not, remove the inconsistent formulas
    # This function takes as an input a beliefset (like ['p','¬q','p -> q', 'p -> r']) and returns 2 things:
    # 1. First, it returns the consistent beliefset (in that case it will return ['p','¬q', 'p -> r'], since 'p -> q' is not consistent with p and ¬q)
    # 2. It will return the value of each element (in that case it will return {p:True, q:False, r:True})

    def check_beliefset(self, n_beliefset):
        beliefset = n_beliefset.copy()
        dic = {}

        for elem in n_beliefset:
            for char in elem:
                if char.isalpha() and char not in dic and char != 'v':
                    dic[char] = []

        # Generate all possible combinations of truth values for each proposition
        combinations = list(itertools.product([False, True], repeat=len(dic)))

        # Create a list of dictionaries with each combination
        list_of_dicts = [{k: v for k, v in zip(dic.keys(), combo)} for combo in combinations]
        # If the beliefset contains the variables p and q, then list_of_dicts = [{p:True,q:True},{p:True,q:False},...]

        list_copy = list_of_dicts.copy()

        for elem in n_beliefset:
            corroboration = []

            for d in list_copy:    
                if d in list_of_dicts:    
                    f = self.get(elem, d)
                    corroboration.append(f)
                    if f == False and len(list_of_dicts) > 1:
                        list_of_dicts.remove(d)

            if all(not x for x in corroboration):
                beliefset.remove(elem)

        return beliefset, list_of_dicts
    
####################################################################################

class Entailment():
    def __init__(self):
        self.beliefset = BeliefSet()

    # Given a formula and a beliefset, checks the entailment (see if the formula is True or False based on the beliefset)
    def check_entailment(self,formula,beliefset):
        bf = self.beliefset
        beliefset, true_false_beliefset = bf.check_beliefset(beliefset)
        formula,true_false_formula = bf.check_beliefset([formula]) 
        for tf in true_false_formula:
            for tf_form in true_false_beliefset:
                is_the_same = True
                for key in tf:
                    if is_the_same == False:
                        break
                    if key in tf_form and tf[key] != tf_form[key]:
                        is_the_same = False
                if is_the_same == True:
                    return True
        return False
    
####################################################################################

# %%
####################################################################################

# LET'S SEE SOME EXAMPLES

####################################################################################

# EXAMPLES IN THE BELIEFSET 

bs = BeliefSet()
print('The beliefset is:',bs.returnset())
proposition,priority = 'p',0
bs.expansion(bs.beliefset, proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = '¬q',1
bs.expansion(bs.beliefset, proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = 'p -> r',2
bs.expansion(bs.beliefset, proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = 'r -> q',1
bs.expansion(bs.beliefset, proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = '(p v r) -> (q)',0
bs.expansion(bs.beliefset, proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition = '¬q'
bs.contraction(bs.beliefset, proposition)
print('The beliefset after contracting the proposition',proposition,'is:',bs.returnset())

proposition,priority = '¬p',0
bs.revision(bs.beliefset, proposition,priority)
print('The beliefset after revising the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = 'r -> p',1
bs.revision(bs.beliefset, proposition,priority)
print('The beliefset after revising the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = 'r -> ¬r',2
bs.expansion(bs.beliefset,  proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())

proposition,priority = 'r',1
bs.expansion(bs.beliefset, proposition,priority)
print('The beliefset after expanding the proposition',proposition,'with priority',priority,'is:',bs.returnset())
print('\n')

####################################################################################

# EXAMPLES WITH THE POSTULATES

#AGM Postulates
# If postulates are correct they return None, else print an error
print('Let\'s check the AGM Postulates')
agm1 = bs.contraction_success(bs.beliefset, 'r')
agm2 = bs.contraction_inclusion(bs.beliefset, 'r')
agm3 = bs.contraction_vacuity(bs.beliefset, 'r')
agm4 = bs.contraction_extensionality(bs.beliefset, 'r','q')

agm5 = bs.revision_success(bs.beliefset, 'r')
agm6 = bs.revision_inclusion(bs.beliefset, 'r')
agm7 = bs.revision_vacuity(bs.beliefset, 'r')
agm8 = bs.revision_consistency(bs.beliefset, 'r')
agm9 = bs.revision_extensionality(bs.beliefset, 'r','q')
print('The postulates are correct' if all(var is None for var in [agm1,agm2,agm3,agm4,agm5,agm6,agm7,agm8,agm9]) else 'There is at least one error')
print('\n')

####################################################################################

# EXAMPLES WITH THE ENTAILMENT

print('Now let\'s check the entailment')
et = Entailment()

formula, beliefset = '¬r -> ¬p',['p', '¬r', 'q -> r','q']
entailment = et.check_entailment(formula,beliefset)
print('The entailement with formula',formula,'and beliefset',beliefset,'is',entailment)

formula, beliefset = 'q <-> r',['p', '¬r', 'q -> r']
entailment = et.check_entailment(formula,beliefset)
print('The entailement with formula',formula,'and beliefset',beliefset,'is',entailment)

formula, beliefset = 'q -> r',['q','r']
entailment = et.check_entailment(formula,beliefset)
print('The entailement with formula',formula,'and beliefset',beliefset,'is',entailment)