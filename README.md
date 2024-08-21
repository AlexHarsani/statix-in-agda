# statix-in-agda

This project is the embedding the declarative semantics of Statix-core and the scope graph, as part of the Master's thesis.

## Prerequisites
- Agda: https://agda.readthedocs.io/en/v2.6.4/getting-started/installation.html
- (Recommended) VS Code: https://code.visualstudio.com
- (Recommended) Agda Mode plugin: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode

## Overview
The project is structured in the following way:
- `src/Constraint.agda`: Includes the definitions of constraints.
- `src/ScopeGraph.ahda`: Includes definitions for scope graphs and fragments.
- `src/ConstraintExperiments.agda`: Includes examples of proofs for the constraints.
- `src/SimplyTypedLambda.agda`: Includes statix-in-agda specification for simple STLC-like language, along with proofs for example programs.
- `src/TypePreservation.agda`: Includes the type preservation proof for simple language with numbers and variables.
- `src/SeminarProject/`: Includes legacy implementation of constraints that was implemented as part of the project for course Seminar Programming Languages.