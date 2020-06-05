using Test

import BDD: variable, is_⊤, is_⊥, is_term, is_var, ⊤, ⊥, reduce!, Diagram, |, restrict, ¬, ∧, ∨,
            valuations

x1, x2, x3 = variable(1), variable(2), variable(3)
X = Diagram[x1, x2, x3]

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
  E = Union{Int, Bool}[1, 2, 3, false, true]
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
