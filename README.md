# A minimal implementation of the Calculus of Inductive Constructions.
The goal of this project is to implement, as simply as possible and inductive type theory, complete with checker and evaluator.
The design of the typechecker deliberately favours simplicity over usability and efficiency. The lexer, parser and prettyprinter do not satisfy these constraints. They are designed for human-readable input and output. As they are adapted from another project, they contain some unused code, such as file position information.
The parser accepts a few syntactial shorthands for lambda- and Pi expressions.

# Features
- Axiom declarations
- Top level definitions
- Data declarations for inductive families. The typechecker will compute the corresponding eliminator

# Limitations
- No large eliminations. These are commonly used to refute absurd equalities (0 = 1), but this also can be done using a single axiom without compromising canonicity.
- No inference or bidirectional typechecking, lambda- and Pi expressions must be fully annotated.
- No parametrized datatypes. Without large eliminations, these are equivalent to their indexed counterparts, but their eliminators are more concise.
