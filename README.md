[![Build Status](https://travis-ci.com/RenatoGeh/BDD.jl.svg?branch=master)](https://travis-ci.com/RenatoGeh/BDD.jl)
[![codecov](https://codecov.io/gh/RenatoGeh/BDD.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/RenatoGeh/BDD.jl)
[![](https://img.shields.io/badge/docs-stable-blue.svg)](https://renatogeh.github.io/BDD.jl/stable)
[![](https://img.shields.io/badge/docs-dev-blue.svg)](https://renatogeh.github.io/BDD.jl/dev)

BinaryDecisionDiagrams.jl (BDD.jl)
======

BDD.jl is a Julia library for manipulating Binary Decision Diagrams (BDDs).

It started as a partial port of `pyddlib` (see https://github.com/thiagopbueno/pyddlib/) but now
has many more features compared to the original package, such as

- Iterating over all possible worlds;
- Functions for easily constructing conjunctions and disjunctions;
- BDD iterators and collection functions;
- Full support for equivalent formulae as keys in a dictionary;
- Shannon's decomposition;
- Variable elimination (aka the `forget` operation);
- Marginalization of a formula given some binary operator (generalization of `forget`);
- Functions for identifying a BDD's scope and verifying a variable's membership;
- Extracting conjunctions as bit arrays;
- Constructors for cardinality constraint formulae (at least, at most and exactly).

The following are references used in this package and the original library.

[1] Bryant, Randal E. **Graph-based algorithms for boolean function
manipulation**. Computers, IEEE Transactions on 100, no. 8 (1986):
677-691.

[2] Brace, Karl S., Richard L. Rudell, and Randal E. Bryant. **Efficient
implementation of a BDD package**. In Proceedings of the 27th ACM/IEEE
design automation conference, pp. 40-45. ACM, 1991.

Install
-------

It is required to have Julia installed.

This package is available on the Julia General Registries.

```bash
  $ julia -e 'using Pkg; Pkg.add("BinaryDecisionDiagrams")'
```

Alternatively, you may add this repository manualy.

```bash
  $ julia -e 'using Pkg; Pkg.add("https://github.com/RenatoGeh/BDD.jl")'
```

Testing
-------

```bash
  $ julia -e 'using Pkg; Pkg.test("BinaryDecisionDiagrams")'
```

Usage
-----

You create BDDs from constants and variables by composing boolean
functions with logical operations AND (∧), OR (∨), XOR (⊻) and
negation (¬).

See `test/runtests.jl` for a comprehensive collection of examples on each feature. It is highly
recommended you check the [docs](https://renatogeh.github.io/BDD.jl/stable), since the snippet
below does not cover all features.

```julia
  import BDD: ⊤, ⊥, variable, ∧, ∨, ⊻, ¬, |
  # For preserving namespace, use 'using BDD' instead.

  println("== True ==")
  println(⊤)
  println("== False ==")
  println(⊥)

  x1 = variable(1)
  x2 = variable(2)
  x3 = variable(3)
  println("=== x1 ===")
  println(x1)

  println("=== ¬x1 ===")
  println(¬x1)

  println("=== x1 ∧ x2 ===")
  println(x1 ∧ x2)

  println("=== x1 ∨ x2 ===")
  println(x1 ∨ x2)

  println("=== x1 ⊻ x2 ===")
  println(x1 ⊻ x2)

  bdd1 = ¬x1 ∨ (x2 ∧ ¬x3)
  if bdd1 ∧ ⊤ == bdd1
    println("True is the neutral element for AND operation")
  end

  bdd2 = ¬(¬x2) ∧ ¬(x1 ∨ x3)
  if bdd2 ∨ zero == bdd2
    println("False is the neutral element for OR operation")
  end

  bdd3 = x1 ∧ ¬x1
  if is_⊥(bdd3)
    println("You can check contradiction with is_⊥")
  end

  bdd4 = x1 ∨ ¬x1
  if is_⊤(bdd4):
    println("You can check tautology with is_⊤")
  end

  bdd5 = ¬(x1 ∨ ¬(x2 ∧ ¬x3))
  if is_⊥(bdd5 ⊻ bdd5)
    println("You can check equivalence with XOR")
  end

  if (x1 ∧ x2) == (x2 ∧ x1)
    println("Commutative law works for boolean functions")
  end

  if x1 ∧ (x2 ∧ x3) == (x1 ∧ x2) ∧ x3
    println("Associative law works for boolean functions")
  end

  if (x1 ∧ (x2 ∨ x3)) == ((x1 ∧ x2) ∨ (x1 ∧ x3))
    println("Distributivity law works: AND distributes over OR")
  end

  if (x1 ∨ (x2 ∧ x3)) == ((x1 ∨ x2) ∧ (x1 ∨ x3))
    println("Distributivity law works: OR distributes over AND")
  end

  bdd6 = ¬(x1 ∧ ¬(¬x2 ∨ x3))
  valuation1 = Dict{Int, Bool}(1 => true, 2 => true, 3 => false)

  if is_⊥(bdd6|valuation1)
    println("You can evaluate the function either with | or function restrict!")
  end

  valuation2 = Dict{Int, Bool}(1 => True)
  if bdd6|valuation2 == ¬x2 ∨ x3:
    println("You can also partially evaluate the function with restrict")
  end
```

LICENSE
-------

See https://github.com/thiagopbueno/pyddlib/ for the original license.
A copy is added to this repository.
