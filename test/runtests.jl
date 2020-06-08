using Test
using Random

import BDD: variable, is_⊤, is_⊥, is_term, is_var, ⊤, ⊥, reduce!, Diagram, |, restrict, ¬, ∧, ∨,
            valuations, conjunctions, convals

x1, x2, x3 = variable(1), variable(2), variable(3)
X = Diagram[x1, x2, x3]

@testset "Valuations" begin
  Random.seed!(101)
  for i ∈ 1:50
    Sc = Random.randsubseq(collect(1:10), 0.5)
    n = length(Sc)
    local p::Int64 = 0
    for (j, x) ∈ enumerate(valuations(Sc))
      @test Set{Int}(keys(x)) == Set{Int}(Sc)
      z = count_zeros(p) - 64 + n
      @test count(y -> y.second, x) == n - z
      @test count(y -> !y.second, x) == z
      p += 1
    end
  end
end

@testset "Conjunctions" begin
  y1, y2, y3 = variable(1), variable(2), variable(3)
  Sc = Int[1, 2, 3]
  E = Diagram[¬y1 ∧ ¬y2 ∧ ¬y3, y1 ∧ ¬y2 ∧ ¬y3, ¬y1 ∧ y2 ∧ ¬y3, y1 ∧ y2 ∧ ¬y3, ¬y1 ∧ ¬y2 ∧ y3,
              y1 ∧ ¬y2 ∧ y3, ¬y1 ∧ y2 ∧ y3, y1 ∧ y2 ∧ y3]
  for (i, α) ∈ enumerate(conjunctions(Sc))
    @test α == E[i]
    for x ∈ valuations(Sc) @test α|x == E[i]|x end
  end
end

@testset "Convals" begin
  y1, y2, y3 = variable(1), variable(2), variable(3)
  Sc = Int[1, 2, 3]
  E = Diagram[¬y1 ∧ ¬y2 ∧ ¬y3, y1 ∧ ¬y2 ∧ ¬y3, ¬y1 ∧ y2 ∧ ¬y3, y1 ∧ y2 ∧ ¬y3, ¬y1 ∧ ¬y2 ∧ y3,
              y1 ∧ ¬y2 ∧ y3, ¬y1 ∧ y2 ∧ y3, y1 ∧ y2 ∧ y3]
  for (i, P) ∈ enumerate(convals(Sc))
    α, x = P
    @test α == E[i]
    for y ∈ valuations(Sc) @test α|y == E[i]|y end
    n = length(Sc)
    z = count_zeros(i-1) - 64 + n
    @test Set{Int}(keys(x)) == Set{Int}(Sc)
    @test count(y -> y.second, x) == n - z
    @test count(y -> !y.second, x) == z
  end
end

@testset "Terminal ⊤" begin
  @test is_⊤(⊤)
  @test !is_⊥(⊤)
  @test is_term(⊤)
  @test !is_var(⊤)
  @test !isdefined(⊤, :high)
  @test !isdefined(⊤, :low)
  @test ⊤.value
  @test ⊤.index == -1
end

@testset "Terminal ⊥" begin
  @test is_⊥(⊥)
  @test !is_⊤(⊥)
  @test is_term(⊥)
  @test !is_var(⊥)
  @test !isdefined(⊥, :high)
  @test !isdefined(⊥, :low)
  @test !⊥.value
  @test ⊥.index == -1
end

@testset "Variable" begin
  for (i, v) ∈ enumerate(X)
    @test is_var(v)
    @test !is_term(v)
    @test !is_⊤(v)
    @test !is_⊥(v)
    @test v.index == i
    @test v.high.value
    @test !v.low.value
  end
end

@testset "Reduce" begin
  @test reduce!(⊤) == ⊤
  @test reduce!(⊥) == ⊥

  for v ∈ X @test reduce!(v) == v end

  a = Diagram(3, ⊥, ⊤)
  b = Diagram(3, ⊥, ⊤)
  c = Diagram(2, b, a)
  d = Diagram(2, ⊥, b)
  e = Diagram(1, d, c)
  R = reduce!(e)
  E = Union{Int, Bool}[1, 2, false, 3, true]
  i = 1
  foreach(function(α::Diagram)
            v = E[i]
            if is_term(α) @test v == α.value
            else @test v == α.index end
            i += 1
          end, R)
end

@testset "Restrict" begin
  Y = Dict{Int, Bool}(1 => true, 2 => false, 3 => true)

  @test ⊤|Y == ⊤
  @test ⊥|Y == ⊥

  for (i, x) ∈ enumerate(X)
    if Y[i] @test x|Y == ⊤
    else @test x|Y == ⊥ end
  end

  mkeg(P::Vararg{Pair{Int, Bool}})::Vector{Dict{Int, Bool}} = collect(Dict{Int, Bool}.(P))
  mkeg!(P::Vararg{Pair{Int, Bool}})::Dict{Int, Bool} = Dict{Int, Bool}(P)

  f1 = x1 ∧ ¬x2
  Y = mkeg(1 => false, 2 => false)
  @test f1|Y[1] == ⊥
  @test f1|Y[2] == x1
  @test f1|merge(Y...) == ⊥

  Y = mkeg(1 => false, 2 => true)
  @test f1|Y[1] == ⊥
  @test f1|Y[2] == ⊥
  @test f1|merge(Y...) == ⊥

  Y = mkeg(1 => true, 2 => false)
  @test f1|Y[1] == ¬x2
  @test f1|Y[2] == x1
  @test f1|merge(Y...) == ⊤

  Y = mkeg(1 => true, 2 => true)
  @test f1|Y[1] == ¬x2
  @test f1|Y[2] == ⊥
  @test f1|merge(Y...) == ⊥

  f2 = x2 ∧ ¬x3
  Y = mkeg!(1 => false, 4 => false)
  @test f2|Y == f2
  Y = mkeg!(1 => false, 4 => true)
  @test f2|Y == f2
  Y = mkeg!(1 => true, 4 => false)
  @test f2|Y == f2
  Y = mkeg!(1 => true, 4 => true)
  @test f2|Y == f2

  f3 = ¬x2 ∨ x3
  E = Diagram[⊤, ⊤, ⊥, ⊥, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊥, ⊥, ⊤, ⊤, ⊤, ⊤]
  for (i, y) ∈ enumerate(valuations(1:4)) f3|y == E[i] end
end

@testset "Negate" begin
  @test ⊤ == ¬⊥
  @test ⊥ == ¬⊤

  X′ = Diagram[¬x for x ∈ X]
  for (i, x) ∈ enumerate(X′)
    @test !is_term(x)
    @test x.index == i
    @test !x.high.value
    @test x.low.value
  end

  a = Diagram(3, ⊥, ⊤)
  b = Diagram(2, ⊥, a)
  c = Diagram(1, b, a)
  d = ¬c
  E = Union{Int, Bool}[1, 2, true, 3, false, 3]
  i = 1
  foreach(function(α::Diagram)
            v = E[i]
            if is_term(α) @test v == α.value
            else @test v == α.index end
            i += 1
          end, d)
end

@testset "Conjunction" begin
  # Idempotency.
  @test ⊤ ∧ ⊤ == ⊤
  @test ⊥ ∧ ⊥ == ⊥
  @test x1 ∧ x1 == x1
  @test x2 ∧ x2 == x2
  @test x3 ∧ x3 == x3
  a = Diagram(3, ⊥, ⊤)
  b = Diagram(2, ⊥, a)
  c = Diagram(1, b, a)
  @test c ∧ c == c

  # Commutative.
  @test ⊥ ∧ ⊤ == ⊤ ∧ ⊥
  @test x1 ∧ x2 == x2 ∧ x1
  @test (x1 ∧ x2) ∧ x3 == x3 ∧ (x1 ∧ x2)
  @test c ∧ (x2 ∧ ¬x3) == (x2 ∧ ¬x3) ∧ c

  # Associative.
  @test x1 ∧ (x2 ∧ x3) == (x1 ∧ x2) ∧ x3
  @test ¬x1 ∧ (x2 ∧ x3) == (¬x1 ∧ x2) ∧ x3
  @test x1 ∧ (¬x2 ∧ x3) == (x1 ∧ ¬x2) ∧ x3
  @test x1 ∧ (x2 ∧ ¬x3) == (x1 ∧ x2) ∧ ¬x3

  # Neutral element.
  @test x1 ∧ ⊤ == x1
  @test x2 ∧ ⊤ == x2
  @test x3 ∧ ⊤ == x3
  @test ¬x1 ∧ ⊤ == ¬x1
  @test ¬x2 ∧ ⊤ == ¬x2
  @test ¬x3 ∧ ⊤ == ¬x3
  @test (x1 ∧ x2 ∧ x3) ∧ ⊤ == x1 ∧ x2 ∧ x3
  @test (¬x1 ∧ ¬x2 ∧ ¬x3) ∧ ⊤ == ¬x1 ∧ ¬x2 ∧ ¬x3
  @test c ∧ ⊤ == c

  # Opposite element.
  @test x1 ∧ ¬x1 == ⊥
  @test ¬x2 ∧ x2 == ⊥
  @test ¬x3 ∧ x3 == ⊥
  @test c ∧ ¬c == ⊥
  @test ¬(x1 ∧ ¬x3 ∧ x2) ∧ (x1 ∧ ¬x3 ∧ x2) == ⊥
  @test ¬x1 ∧ ¬¬x1 == ⊥
  @test ¬(¬x2) ∧ ¬x2 == ⊥
  @test ¬(¬x3) ∧ ¬x3 == ⊥
  @test ¬c ∧ ¬¬c == ⊥
  @test ¬¬(x1 ∧ ¬x3 ∧ x2) ∧ ¬(x1 ∧ ¬x3 ∧ x2) == ⊥

  # Distributive conjunction over disjunction.
  @test x1 ∧ (x2 ∨ x3) == (x1 ∧ x2) ∨ (x1 ∧ x3)
  @test c ∧ (x2 ∨ x3) == (c ∧ x2) ∨ (c ∧ x3)
  @test x1 ∧ (c ∨ x3) == (x1 ∧ c) ∨ (x1 ∧ x3)
  @test x1 ∧ (x2 ∨ c) == (x1 ∧ x2) ∨ (x1 ∧ c)
end

@testset "Disjunction" begin
  # Idempotency.
  @test ⊤ ∨ ⊤ == ⊤
  @test ⊥ ∨ ⊥ == ⊥
  @test x1 ∨ x1 == x1
  @test x2 ∨ x2 == x2
  @test x3 ∨ x3 == x3
  a = Diagram(3, ⊥, ⊤)
  b = Diagram(2, ⊥, a)
  c = Diagram(1, b, a)
  @test c ∨ c == c

  # Commutative.
  @test ⊥ ∨ ⊤ == ⊤ ∨ ⊥
  @test x1 ∨ x2 == x2 ∨ x1
  @test (x1 ∨ x2) ∨ x3 == x3 ∨ (x1 ∨ x2)
  @test c ∨ (x2 ∨ ¬x3) == (x2 ∨ ¬x3) ∨ c

  # Associative.
  @test x1 ∨ (x2 ∨ x3) == (x1 ∨ x2) ∨ x3
  @test ¬x1 ∨ (x2 ∨ x3) == (¬x1 ∨ x2) ∨ x3
  @test x1 ∨ (¬x2 ∨ x3) == (x1 ∨ ¬x2) ∨ x3
  @test x1 ∨ (x2 ∨ ¬x3) == (x1 ∨ x2) ∨ ¬x3

  # Neutral element.
  @test x1 ∨ ⊥ == x1
  @test x2 ∨ ⊥ == x2
  @test x3 ∨ ⊥ == x3
  @test ¬x1 ∨ ⊥ == ¬x1
  @test ¬x2 ∨ ⊥ == ¬x2
  @test ¬x3 ∨ ⊥ == ¬x3
  @test (x1 ∨ x2 ∨ x3) ∨ ⊥ == x1 ∨ x2 ∨ x3
  @test (¬x1 ∨ ¬x2 ∨ ¬x3) ∨ ⊥ == ¬x1 ∨ ¬x2 ∨ ¬x3
  @test c ∨ ⊥ == c

  # Opposite element.
  @test x1 ∨ ¬x1 == ⊤
  @test ¬x2 ∨ x2 == ⊤
  @test ¬x3 ∨ x3 == ⊤
  @test c ∨ ¬c == ⊤
  @test ¬(x1 ∨ ¬x3 ∨ x2) ∨ (x1 ∨ ¬x3 ∨ x2) == ⊤
  @test ¬x1 ∨ ¬¬x1 == ⊤
  @test ¬(¬x2) ∨ ¬x2 == ⊤
  @test ¬(¬x3) ∨ ¬x3 == ⊤
  @test ¬c ∨ ¬¬c == ⊤
  @test ¬¬(x1 ∨ ¬x3 ∨ x2) ∨ ¬(x1 ∨ ¬x3 ∨ x2) == ⊤

  # Distributive disjunction over conjunction.
  @test x1 ∨ (x2 ∧ x3) == (x1 ∨ x2) ∧ (x1 ∨ x3)
  @test c ∨ (x2 ∧ x3) == (c ∨ x2) ∧ (c ∨ x3)
  @test x1 ∨ (c ∧ x3) == (x1 ∨ c) ∧ (x1 ∨ x3)
  @test x1 ∨ (x2 ∧ c) == (x1 ∨ x2) ∧ (x1 ∨ c)
end

@testset "XOR" begin
  # Idempotency.
  @test ⊤ ⊻ ⊤ == ⊥
  @test ⊥ ⊻ ⊥ == ⊥
  @test x1 ⊻ x1 == ⊥
  @test x2 ⊻ x2 == ⊥
  @test x3 ⊻ x3 == ⊥
  a = Diagram(3, ⊥, ⊤)
  b = Diagram(2, ⊥, a)
  c = Diagram(1, b, a)
  @test c ⊻ c == ⊥

  # Commutative.
  @test ⊥ ⊻ ⊤ == ⊤ ⊻ ⊥
  @test x1 ⊻ x2 == x2 ⊻ x1
  @test (x1 ⊻ x2) ⊻ x3 == x3 ⊻ (x1 ⊻ x2)
  @test c ⊻ (x2 ⊻ ¬x3) == (x2 ⊻ ¬x3) ⊻ c

  # Associative.
  @test x1 ⊻ (x2 ⊻ x3) == (x1 ⊻ x2) ⊻ x3
  @test ¬x1 ⊻ (x2 ⊻ x3) == (¬x1 ⊻ x2) ⊻ x3
  @test x1 ⊻ (¬x2 ⊻ x3) == (x1 ⊻ ¬x2) ⊻ x3
  @test x1 ⊻ (x2 ⊻ ¬x3) == (x1 ⊻ x2) ⊻ ¬x3

  # Neutral element.
  @test x1 ⊻ ⊥ == x1
  @test x2 ⊻ ⊥ == x2
  @test x3 ⊻ ⊥ == x3
  @test ¬x1 ⊻ ⊥ == ¬x1
  @test ¬x2 ⊻ ⊥ == ¬x2
  @test ¬x3 ⊻ ⊥ == ¬x3
  @test (x1 ⊻ x2 ⊻ x3) ⊻ ⊥ == x1 ⊻ x2 ⊻ x3
  @test (¬x1 ⊻ ¬x2 ⊻ ¬x3) ⊻ ⊥ == ¬x1 ⊻ ¬x2 ⊻ ¬x3
  @test c ⊻ ⊥ == c

  # Opposite element.
  @test x1 ⊻ ¬x1 == ⊤
  @test ¬x2 ⊻ x2 == ⊤
  @test ¬x3 ⊻ x3 == ⊤
  @test c ⊻ ¬c == ⊤
  @test ¬(x1 ⊻ ¬x3 ⊻ x2) ⊻ (x1 ⊻ ¬x3 ⊻ x2) == ⊤
  @test ¬x1 ⊻ ¬¬x1 == ⊤
  @test ¬(¬x2) ⊻ ¬x2 == ⊤
  @test ¬(¬x3) ⊻ ¬x3 == ⊤
  @test ¬c ⊻ ¬¬c == ⊤
  @test ¬¬(x1 ⊻ ¬x3 ⊻ x2) ⊻ ¬(x1 ⊻ ¬x3 ⊻ x2) == ⊤
end

@testset "Shannon decomposition" begin
  ϕ = x1 ∧ x2 ∨ x3
end
