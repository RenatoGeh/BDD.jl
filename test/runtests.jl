using Test

import BDD: variable, is_⊤, is_⊥, is_term, is_var, ⊤, ⊥, reduce!, Diagram

x1, x2, x3 = variable(1), variable(2), variable(3)

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
  for (i, v) ∈ enumerate([x1, x2, x3])
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

  for v ∈ [x1, x2, x3] @test reduce!(v) == v end

  a = Diagram(3, ⊥, ⊤)
  b = Diagram(3, ⊥, ⊤)
  c = Diagram(2, b, a)
  d = Diagram(2, ⊥, b)
  e = Diagram(1, d, c)
  R = reduce!(e)
  E = Union{Int, Bool}[1, 2, 3, false, true]
  i = 1
  println(R)
  foreach(function(α::Diagram)
            v = E[i]
            if is_term(α) @test v == α.value
            else @test v == α.index end
            i += 1
          end, R)
end
