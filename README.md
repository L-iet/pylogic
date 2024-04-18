# Pylogic

This is a simple proof assistant for propositional and predicate logic. The goal is to be able to formalise some statements from real analysis and prove them using this tool.

## Proof search

This subproject is about searching for proofs of predicates. The `pylogic.proposition.proof_search` module contains the `proof_search` function which uses a depth-first search to find a proof of a given proposition.

## Installation

- Clone the repository
- Install the requirements using `pip install -r requirements.txt`
- To run the proof_search test cases, run `python proof_search_tests.py`
- You can also check out other demos of Pylogic in `main.py` and `pylogic_demo.ipynb`