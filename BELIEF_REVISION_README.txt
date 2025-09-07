BELIEFSET AND ENTAILMENT EXPLANATION AND USAGE GUIDE

1. Introduction
BeliefSet is a Python class designed to handle belief sets in formal logic. It includes methods for expanding, contracting, and revising belief sets according to the AGM postulates. Additionally, Entailment is a class for checking entailment between a formula and a belief set.

2. Explanation on How to Insert Formulas Correctly in the BeliefSet
All variables should be lowercase letters from the alphabet except for 'v' (v is used for 'or' operations).
If the formula is something simple, like 'p', '¬q', 'p -> q',..., then no parentheses are needed.
Simple formulas are:
    1. Proposition: 'p'
    2. Negation: '¬p'
    3. Implication: 'p -> q', '¬p -> q', 'p -> ¬q', '¬p -> ¬q'
    4. Disjunction: 'p v q'
    5. Conjunction: 'p ^ q'
    6. If and only if: 'p <-> q'
If more complex formulas are written, then parentheses are needed.
More complex formulas are: (note that x and y can be any of the simple formulas)
    7. Complex negation: '¬(x)'
    8. Complex implication: '(x) -> (y)'
    9. Complex disjunction: '(x) v (y)'
    10. Complex conjunction: '(x) ^ (y)'
    11. Complex if and only if: '(x) <-> (y)'

Double negation (¬¬p) is not allowed, and the letter 'v' cannot be used as a belief since it represents logical 'or' operations.

3. Regular Expressions
The code utilizes regular expressions to match different patterns of formulas, such as propositions, negations, implications, etc. These patterns ensure correct parsing and handling of formulas.

4. BeliefSet Class
- Methods:
    - expansion: Add a proposition to the belief set at a specified priority.
    - contraction: Remove a proposition from the belief set if it exists.
    - revision: Revise the belief set with a new proposition at a specified priority.
    - AGM Postulates: Check consistency and correctness of belief set operations based on AGM postulates.
    - check_beliefset: Verify consistency of the belief set and return the consistent set along with truth values for each proposition.
    - empty: Clear the belief set.
    - returnset: Get the current belief set.

5. Entailment Class
- Methods:
    - check_entailment: Check if a formula entails from a belief set.

6. Example Usage
The code includes examples demonstrating how to use the BeliefSet and Entailment classes, along with testing the AGM postulates and entailment checks.

7. AGM Postulates Testing
The code verifies the correctness of belief set operations against AGM postulates, ensuring consistency and correctness.

8. Entailment Checking
The code includes functionality to check if a given formula entails from a belief set, providing insights into logical entailment relationships.

For detailed examples and usage instructions, refer to the code comments and example executions.
