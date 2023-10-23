# statix-in-agda

This project models the part of declarative semantics of Statix-core, based on the Figure 7 of the paper 'Knowing When to Ask'(to be referred as 'the paper') [1]. 

![Figure 7](/doc/declarative_semantics.png)

## Prerequisites
- Agda: https://agda.readthedocs.io/en/v2.6.4/getting-started/installation.html
- (Recommended) VS Code: https://code.visualstudio.com
- (Recommended) Agda Mode plugin: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode

## Overview
The project is structured in the following way:
- `Graph.agda`: This module contains necessary data types that model the scope graph and related structures.
- `Constraint.agda`: This module contains the definition of a subset of statix-core constraints, the declarational semantics, as well as the helper functions `substitute`, `replaceTerm` and `mapReplaceTerm`.
- `Proofs.agda`: This module contains satisfiability proofs for concrete instances of constraints.

## Implementation Details

### Term & TermSet

- In `src/Graph.agda`
- Term can be a variable, a compound term consisting of one or more terms, a scope graph label, or a scope graph node
- TermSet is a set of terms. It is also necessary to (for now) postulate a number of properties.
    - `Relation`: this is necessary for the `min` property in the minimum constraint.
    - `WellFormedTermSet`: As TermSet is defined using list, we need a property of well-formedness of a set. This means that there are no duplicate values.
    - `minTermSet`: This property represents the min property from the page 11 in the paper [1]. This is necessary for the minimum constraint.

### GraphFragment

- In `src/Graph.agda`
- Graph fragment consists of subset of graph's nodes and edges
- Similarly to term set, it is necessary to define a few properties and an operator for the graph fragments:
    - `Empty`: this property states that graph fragment is empty
    - `WellFormedness`: this property states that graph is well formed, which means that there are no duplicate values of nodes and edges
    - `Partition`: this property states that two graph fragments are a partition of a larger graph fragment
    - `_⊔_`: this operator represents the disjoint union of graph fragments

### Constraint

- In `src/Constraint.agda`
- Data type Constraint defines a subset of Statix-core constraints
- These are: emp, false, separating conjunction, term equality, exists, singleton, minimum, forall
- Syntax is based on the figure 6 of the paper [1]

### Satisfies

- In `src/Constraint.agda`
- Defines satisfiability for each of the constraints based on figure 7 of the paper [1]

### Proofs

- In `src/Proofs.agda`
- These proofs demonstrate the use of the satisfiability property on concrete examples of constraints

## References
[1]: Rouvoet, A., Van Antwerpen, H., Bach Poulsen, C., Krebbers, R., & Visser, E. (2020). Knowing when to ask: sound scheduling of name resolution in type checkers derived from declarative specifications. Proceedings of the ACM on Programming Languages, 4(OOPSLA), 1-28.