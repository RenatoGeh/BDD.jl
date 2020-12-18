module BinaryDecisionDiagrams

nextid = 1

mutable struct Diagram
  "Root vertex variable index (-1 if terminal vertex)."
  index::Int
  "Low child vertex of BDD (undef if terminal vertex)."
  low::Diagram
  "High child vertex of BDD (undef if terminal vertex)."
  high::Diagram
  "Terminal boolean value."
  value::Bool
  "Unique identifier."
  id::Int
  "Constructs a terminal."
  function Diagram(v::Bool)::Diagram
    α = new()
    global nextid
    α.index, α.value, α.id = -1, v, nextid
    nextid = (nextid + 1) % typemax(Int)
    return α
  end
  "Constructs a variable."
  function Diagram(i::Int, low::Diagram, high::Diagram)::Diagram
    α = new()
    global nextid
    α.index, α.low, α.high, α.id = i, low, high, nextid
    nextid = (nextid + 1) % typemax(Int)
    return α
  end
end
export Diagram

const ⊤ = Diagram(true)
const ⊥ = Diagram(false)
export ⊤, ⊥

"Returns a shallow hash for the given node (not BDD as a whole)."
@inline shallowhash(α::Diagram, h::UInt = UInt64(0)) = hash((α.id, α.value, α.index), h)
export shallowhash

"Returns a unique hash for the whole BDD."
function Base.hash(α::Diagram, h::UInt)::UInt
  H = Tuple{Bool, Int}[]
  foreach(x -> push!(H, (is_term(x) ? x.value : false, x.index)), α)
  return hash(H, h)
end

"Returns whether this Diagram node is terminal."
@inline is_term(α::Diagram)::Bool = !isdefined(α, :low) && !isdefined(α, :high)
export is_term

"Returns whether the given Diagram node represents a ⊤."
@inline is_⊤(α::Diagram)::Bool = is_term(α) && α.value
export is_⊤

"Returns whether the given Diagram node represents a ⊥."
@inline is_⊥(α::Diagram)::Bool = is_term(α) && !α.value
export is_⊥

"Returns whether the given Diagram node represents a variable."
@inline is_var(α::Diagram)::Bool = (isdefined(α, :low) && is_⊥(α.low)) && (isdefined(α, :high) && is_⊤(α.high))
"Returns whether the given Diagram node represents a literal."
@inline is_lit(α::Diagram)::Bool = isdefined(α, :low) && isdefined(α, :high) && is_term(α.low) && is_term(α.high)
"Returns whether the given Diagram node is an atomic formula (i.e. a variable, ⊥, ⊤, or literal)."
@inline is_atom(α::Diagram)::Bool = is_term(α) || is_lit(α)
export is_var, is_lit, is_atom

"Negates this boolean function."
@inline (¬)(α::Diagram)::Diagram = is_⊤(α) ? ⊥ : is_⊥(α) ? ⊤ : Diagram(α.index, ¬α.low, ¬α.high)
@inline (¬)(x::Int)::Diagram = x > 0 ? Diagram(x, ⊤, ⊥) : x < 0 ? Diagram(-x, ⊥, ⊤) : ⊥
@inline (¬)(x::Bool)::Bool = !x
export ¬

"Returns a conjunction over the given boolean functions."
@inline (∧)(α::Diagram, β::Diagram)::Diagram = apply(α, β, &)
@inline (∧)(x::Int, β::Diagram)::Diagram = apply(variable(x), β, &)
@inline (∧)(α::Diagram, x::Int)::Diagram = apply(α, variable(x), &)
@inline (∧)(x::Int, y::Int)::Diagram = apply(variable(x), variable(y), &)
@inline (∧)(x::Bool, y::Bool)::Bool = x & y
export ∧
"Returns a conjunction over the given boolean functions."
@inline and(α::Diagram, β::Diagram)::Diagram = α ∧ β
@inline and(x::Int, β::Diagram)::Diagram = x ∧ β
@inline and(α::Diagram, x::Int)::Diagram = α ∧ x
@inline and(x::Int, y::Int)::Diagram = x ∧ y
function and(Φ::Vararg{Diagram})::Diagram
  α = first(Φ)
  for i ∈ 2:length(Φ) α = α ∧ Φ[i] end
  return α
end
@inline and(Φ::Vector{Diagram})::Diagram = and(Φ...)
@inline and(Φ::Vararg{Int})::Diagram = and(variable.(Φ)...)
@inline and(Φ::Vector{Int})::Diagram = and(variable.(Φ)...)
function and(Φ::Vararg{Union{Int, Diagram}})::Diagram
  f = first(Φ)
  α = f isa Int ? variable(f) : f
  for i ∈ 2:length(Φ) α = α ∧ Φ[i] end
  return α
end
export and

"Returns a disjunction over the given boolean functions."
@inline (∨)(α::Diagram, β::Diagram)::Diagram = apply(α, β, |)
@inline (∨)(x::Int, β::Diagram)::Diagram = apply(variable(x), β, |)
@inline (∨)(α::Diagram, x::Int)::Diagram = apply(α, variable(x), |)
@inline (∨)(x::Int, y::Int)::Diagram = apply(variable(x), variable(y), |)
@inline (∨)(x::Bool, y::Bool)::Bool = x | y
export ∨
"Returns a disjunction over the given boolean functions."
@inline or(α::Diagram, β::Diagram)::Diagram = α ∨ β
@inline or(x::Int, β::Diagram)::Diagram = x ∨ β
@inline or(α::Diagram, x::Int)::Diagram = α ∨ x
@inline or(x::Int, y::Int)::Diagram = x ∨ y
@inline function or(Φ::Vararg{Diagram})::Diagram
  α = first(Φ)
  for i ∈ 2:length(Φ) α = α ∨ Φ[i] end
  return α
end
@inline or(Φ::Vector{Diagram})::Diagram = or(Φ...)
@inline or(Φ::Vararg{Int})::Diagram = or(variable.(Φ)...)
@inline or(Φ::Vector{Int})::Diagram = or(variable.(Φ)...)
function or(Φ::Vararg{Union{Int, Diagram}})::Diagram
  f = first(Φ)
  α = f isa Int ? variable(f) : f
  for i ∈ 2:length(Φ) α = α ∨ Φ[i] end
  return α
end
export or

"Returns a xor of the given boolean functions."
@inline Base.:⊻(α::Diagram, β::Diagram)::Diagram = apply(α, β, ⊻)
@inline Base.:⊻(x::Int, β::Diagram)::Diagram = apply(variable(x), β, ⊻)
@inline Base.:⊻(α::Diagram, x::Int)::Diagram = apply(α, variable(x), ⊻)
@inline Base.:⊻(x::Int, y::Int)::Diagram = apply(variable(x), variable(y), ⊻)

"Returns whether the two given boolean functions are equivalent."
@inline Base.:(==)(α::Diagram, β::Diagram)::Bool = is_⊤(apply(α, β, ==))
@inline Base.:(==)(x::Int, β::Diagram)::Bool = is_var(β) && β.index == x && ((x > 0 && β.low == ⊥ && β.high == ⊤) || (x < 0 && β.low == ⊤ && β.high == ⊥))
@inline Base.:(==)(α::Diagram, y::Int)::Bool = y == α
@inline Base.isequal(α::Diagram, β::Diagram)::Bool = α == β
@inline Base.isequal(x::Int, β::Diagram)::Bool = x == β
@inline Base.isequal(α::Diagram, y::Int)::Bool = y == α

"Returns whether the two given boolean functions are not equivalent."
@inline Base.:(!=)(α::Diagram, β::Diagram)::Bool = !(α == β)
@inline Base.:(!=)(x::Int, β::Diagram)::Bool = !(x == β)
@inline Base.:(!=)(α::Diagram, y::Int)::Bool = !(y == α)

"Returns a new terminal node of given boolean value."
@inline terminal(v::Bool)::Diagram = Diagram(v)
export terminal

"Returns a Diagram representing a single variable. If negative, negate variable."
@inline variable(i::Int)::Diagram = i > 0 ? Diagram(i, ⊥, ⊤) : Diagram(-i, ⊤, ⊥)
export variable

"Returns 0 if x is not a literal; else returns the literal's sign."
@inline Base.sign(x::Diagram) = !is_lit(x) ? 0 : x.low == ⊥ ? 1 : -1
@inline Base.signbit(x::Diagram) = sign(x) == -1
"Returns 0 if x is not a literal; else returns an integer representation of x."
@inline to_int(x::Diagram) = !is_lit(x) ? 0 : x.low == ⊥ ? x.index : -x.index
export to_int

"Return string representation of Diagram α."
function Base.string(α::Diagram)::String
  s = ""
  S = Tuple{Diagram, Int, Char}[(α, 0, '\0')]
  while !isempty(S)
    v, indent, c = pop!(S)
    for i ∈ 1:indent s *= "|  " end
    s *= c == '\0' ? '@' : c
    if is_term(v)
      s *= " (value=$(v.value), id=$(v.id))\n"
    else
      s *= " (index=$(v.index), id=$(v.id))\n"
      push!(S, (v.high, indent + 1, '+'))
      push!(S, (v.low, indent + 1, '-'))
    end
  end
  return s
end
Base.show(io::Core.IO, α::Diagram) = show(io, string(α))
Base.print(io::Core.IO, α::Diagram) = print(io, string(α))

let V::Set{UInt64}, Q::Vector{Diagram}
  function Base.iterate(α::Diagram, state=1)::Union{Nothing, Tuple{Diagram, Integer}}
    if state == 1
      Q = Diagram[α]
      V = Set{UInt64}(objectid(α))
    end
    if isempty(Q) return nothing end
    v = pop!(Q)
    if !is_term(v)
      l, h = v.low, v.high
      p, q = objectid(l), objectid(h)
      if q ∉ V push!(Q, h); push!(V, q) end
      if p ∉ V push!(Q, l); push!(V, p) end
    end
    return v, state+1
  end
end

function Base.foreach(f::Function, α::Diagram)
  V = Set{UInt64}(shallowhash(α))
  Q = Diagram[α]
  while !isempty(Q)
    v = pop!(Q)
    if !is_term(v)
      l, h = v.low, v.high
      p, q = objectid(l), objectid(h)
      if q ∉ V push!(Q, h); push!(V, q) end
      if p ∉ V push!(Q, l); push!(V, p) end
    end
    f(v)
  end
  nothing
end

function Base.collect(α::Diagram)::Vector{Diagram}
  V = Set{UInt64}(objectid(α))
  Q = Diagram[α]
  C = Vector{Diagram}()
  while !isempty(Q)
    v = pop!(Q)
    if !is_term(v)
      l, h = v.low, v.high
      p, q = objectid(l), objectid(h)
      if q ∉ V push!(Q, h); push!(V, q) end
      if p ∉ V push!(Q, l); push!(V, p) end
    end
    push!(C, v)
  end
  return C
end

"""Reduce a Diagram rooted at α inplace, removing duplicate nodes and redundant sub-trees. Returns
canonical representation of α."""
function reduce!(α::Diagram)::Diagram
  if is_term(α) return α end

  V = Dict{Int, Vector{Diagram}}()
  foreach(function(v::Diagram)
            i = v.index
            haskey(V, i) ? push!(V[i], v) : V[i] = Diagram[v]
          end, α)
  nid = 0
  G = Dict{Int, Diagram}()
  I = sort!(collect(keys(V)), rev=true); pop!(I); pushfirst!(I, -1)
  for i ∈ I
    Q = Vector{Tuple{Tuple{Int, Int}, Diagram}}()
    for v ∈ V[i]
      if is_term(v) push!(Q, ((Int(v.value), -1), v))
      elseif v.low.id == v.high.id v.id = v.low.id
      else push!(Q, ((v.low.id, v.high.id), v)) end
    end
    sort!(Q, by=first)
    local oldk::Tuple{Int, Int} = (-2, -2)
    for (k, v) ∈ Q
      if k == oldk v.id = nid
      else
        nid += 1
        v.id = nid
        G[nid] = v
        if !is_term(v)
          v.low = G[v.low.id]
          v.high = G[v.high.id]
        end
        oldk = k
      end
    end
  end
  return G[α.id]
end
export reduce!

function Base.copy(α::Diagram)::Diagram
  if is_term(α) return is_⊤(α) ? Diagram(true) : Diagram(false) end
  return Diagram(α.index, α.low, α.high)
end

function Base.deepcopy(α::Diagram)::Diagram
  if is_term(α) return is_⊤(α) ? Diagram(true) : Diagram(false) end
  return Diagram(α.index, copy(α.low), copy(α.high))
end

"Returns a Diagram canonical representation of α ⊕ β, where ⊕ is some binary operator."
@inline apply(α::Diagram, β::Diagram, ⊕) = reduce!(apply_step(α, β, ⊕, Dict{Tuple{Int, Int}, Diagram}()))
export apply

"""Recursively computes α ⊕ β. If the result was already computed as an intermediate result, return
the cached result in T."""
function apply_step(α::Diagram, β::Diagram, ⊕, T::Dict{Tuple{Int, Int}, Diagram})::Diagram
  local k::Tuple{Int, Int} = (α.id, β.id)
  if haskey(T, k) return T[k] end

  local r::Diagram
  if is_term(α) && is_term(β) r = Diagram(α.value ⊕ β.value)
  else
    local i::Int = typemax(Int)
    local j::Int = i

    if !is_term(α) i = α.index end
    if !is_term(β) j = β.index end
    m = min(i, j)

    local l1::Diagram, h1::Diagram
    if α.index == m l1, h1 = α.low, α.high
    else l1 = h1 = α end

    local l2::Diagram, h2::Diagram
    if β.index == m l2, h2 = β.low, β.high
    else l2 = h2 = β end

    l = apply_step(l1, l2, ⊕, T)
    h = apply_step(h1, h2, ⊕, T)
    r = Diagram(m, l, h)
  end

  T[k] = r
  return r
end

"Returns a new reduced Diagram restricted to instantiation X."
@inline restrict(α::Diagram, X::Dict{Int, Bool})::Diagram = reduce!(restrict_step(α, X))
@inline restrict(α::Diagram, X::AbstractArray{Int})::Diagram = reduce!(restrict_step(α, X))
@inline restrict(α::Diagram, X::BitVector)::Diagram = reduce!(restrict_step(α, X))
@inline restrict(α::Diagram, X::AbstractArray{Bool})::Diagram = reduce!(restrict_step(α, X))
export restrict
"Returns a new reduced Diagram restricted to instantiation X."
@inline Base.:|(α::Diagram, X::Dict{Int, Bool})::Diagram = restrict(α, X)
@inline Base.:|(α::Diagram, X::AbstractArray{Int})::Diagram = restrict(α, X)
@inline Base.:|(α::Diagram, X::BitVector)::Diagram = restrict(α, X)
@inline Base.:|(α::Diagram, x::Int)::Diagram = restrict(α, Dict{Int, Bool}(x > 0 ? x => true : -x => false))
@inline Base.:|(α::Diagram, X::AbstractArray{Bool})::Diagram = restrict(α, X)
"Returns the evaluation of α given an instantiation X. Returns false if X is not a full instantiation."
@inline (α::Diagram)(X::Dict{Int, Bool})::Bool = is_⊤(restrict(α, X))
@inline (α::Diagram)(X::AbstractArray{Int})::Bool = is_⊤(α|X)
@inline (α::Diagram)(X::BitVector)::Bool = is_⊤(α|X)
@inline (α::Diagram)(x::Int)::Bool = is_⊤(α|x)
@inline (α::Diagram)(X::AbstractArray{Bool})::Bool = is_⊤(α|X)

"Returns a new Diagram restricted to instantiation X."
function restrict_step(α::Diagram, X::Dict{Int, Bool})::Diagram
  if is_term(α) return copy(α) end
  x = α.index
  if !haskey(X, x)
    l = restrict_step(α.low, X)
    h = restrict_step(α.high, X)
    return Diagram(x, l, h)
  end
  if X[x] return restrict_step(α.high, X) end
  return restrict_step(α.low, X)
end

"Returns a new Diagram restricted to instantiation X."
function restrict_step(α::Diagram, X::AbstractArray{Int})::Diagram
  if is_term(α) return copy(α) end
  x = α.index
  if x > length(X)
    l = restrict_step(α.low, X)
    h = restrict_step(α.high, X)
    return Diagram(x, l, h)
  end
  if X[x] > 0 return restrict_step(α.high, X) end
  return restrict_step(α.low, X)
end

"Returns a new Diagram restricted to instantiation X."
function restrict_step(α::Diagram, X::BitVector)::Diagram
  if is_term(α) return copy(α) end
  x = α.index
  if x > length(X)
    l = restrict_step(α.low, X)
    h = restrict_step(α.high, X)
    return Diagram(x, l, h)
  end
  if X[x] return restrict_step(α.high, X) end
  return restrict_step(α.low, X)
end

"Returns a new Diagram restricted to instantiation X."
function restrict_step(α::Diagram, X::AbstractArray{Bool})::Diagram
  if is_term(α) return copy(α) end
  x = α.index
  if x > length(X)
    l = restrict_step(α.low, X)
    h = restrict_step(α.high, X)
    return Diagram(x, l, h)
  end
  if X[x] return restrict_step(α.high, X) end
  return restrict_step(α.low, X)
end

struct Permutations
  V::Vector{Int}
  m::Int
end
@inline Base.length(P::Permutations)::Int = P.m

"Compute all possible valuations of scope V."
@inline valuations(V::Union{Set{Int}, Vector{Int}, UnitRange{Int}}) = Permutations(collect(V), 2^length(V))
export valuations
function Base.iterate(P::Permutations, state=0)::Union{Nothing, Tuple{Dict{Int, Bool}, Int}}
  s = state + 1
  if state == 0 return Dict{Int, Bool}(broadcast(x -> abs(x) => false, P.V)), s end
  if state >= P.m return nothing end
  return Dict{Int, Bool}((i -> P.V[i] => (state >> (i-1)) & 1 == 1).(1:length(P.V))), s
end

"Computes all possible valuations of scope V and returns as a BitMatrix. Up to 64 variables."
function all_valuations(V::Union{Set{Int}, Vector{Int}, UnitRange{Int}})::BitMatrix
  m = length(V)
  n = 2^m
  M = BitMatrix(undef, (n, m))
  for i ∈ 1:n
    p = i-1
    for j ∈ 1:m
      M[i, j] = p & 1
      p >>= 1
    end
  end
  return M
end
export all_valuations

struct ConjoinedPermutations
  V::Vector{Int}
  m::Int
end
@inline Base.length(P::ConjoinedPermutations)::Int = P.m

"Computes all possible valuations of scope V as conjunctions."
@inline conjunctions(V::Union{Set{Int}, Vector{Int}, UnitRange{Int}}) = ConjoinedPermutations(sort!(collect(V)), 2^length(V))
export conjunctions
function Base.iterate(P::ConjoinedPermutations, state=0)::Union{Nothing, Tuple{Diagram, Int}}
  s = state + 1
  if state >= P.m return nothing end
  local V::Vector{Int}
  if state == 0 V = broadcast(-, P.V)
  else V = (i -> (state >> (i-1)) & 1 == 1 ? P.V[i] : -P.V[i]).(1:length(P.V)) end
  local α::Diagram
  f = true
  for v ∈ Iterators.reverse(V)
    if f
      α = variable(v)
      f = false
    else
      α = v > 0 ? Diagram(v, ⊥, α) : Diagram(-v, α, ⊥)
    end
  end
  return α, s
end

struct ConvalPermutations
  V::Vector{Int}
  m::Int
end
@inline Base.length(P::ConvalPermutations) = P.m

"Computes all possible valuations of scope V as both conjunctions and instantiation values."
@inline convals(V::Union{Set{Int}, Vector{Int}, UnitRange{Int}}) = ConvalPermutations(sort!(collect(V)), 2^length(V))
export convals
function Base.iterate(P::ConvalPermutations, state=0)::Union{Nothing, Tuple{Tuple{Diagram, Dict{Int, Bool}}, Int}}
  s = state + 1
  if state >= P.m return nothing end
  local V::Vector{Int}
  if state == 0 V = broadcast(-, P.V)
  else V = (i -> (state >> (i-1)) & 1 == 1 ? P.V[i] : -P.V[i]).(1:length(P.V)) end
  local α::Diagram
  f = true
  for v ∈ Iterators.reverse(V)
    if f
      α = variable(v)
      f = false
    else
      α = v > 0 ? Diagram(v, ⊥, α) : Diagram(-v, α, ⊥)
    end
  end
  return (α, Dict{Int, Bool}((i -> i > 0 ? i => true : -i => false).(V))), s
end

"Performs Shannon's Decomposition on the Diagram α, given a variable to isolate."
function shannon(α::Diagram, v::Int)::Tuple{Diagram, Diagram, Diagram, Diagram}
  return (variable(v), α|Dict{Int, Bool}(v=>true), variable(-v), α|Dict{Int, Bool}(v=>false))
end

"Performs Shannon's Decomposition on the Diagram α, given a set of variables to isolate."
function shannon(α::Diagram, V::Union{Set{Int}, Vector{Int}})::Vector{Tuple{Diagram, Diagram}}
  Δ = Vector{Tuple{Diagram, Diagram}}()
  for (β, X) ∈ convals(V) push!(Δ, (β, α|X)) end
  return Δ
end

"""Performs Shannon's Decomposition on the Diagram α, given a set of variables to isolate. Any
decomposition that results in a ⊥ is discarded."""
function shannon!(α::Diagram, V::Union{Set{Int}, Vector{Int}})::Vector{Tuple{Diagram, Diagram}}
  Δ = Vector{Tuple{Diagram, Diagram}}()
  for (β, X) ∈ convals(V)
    ϕ = α|X
    if is_⊥(ϕ) continue end
    push!(Δ, (β, ϕ))
  end
  return Δ
end

export shannon, shannon!

"Eliminate a variable through disjunction. Equivalent to the expression (ϕ|x ∨ ϕ|¬x)."
@inline eliminate(α::Diagram, v::Int)::Diagram = reduce!(eliminate_step(α, v))
export eliminate
function eliminate_step(α::Diagram, v::Int)::Diagram
  if is_term(α) return copy(α) end
  if α.index == v return α.low ∨ α.high end
  # If idempotent (which is the case), then recursion suffices.
  l = eliminate(α.low, v)
  h = eliminate(α.high, v)
  return Diagram(α.index, l, h)
end

"Marginalize a variable through some binary operation."
@inline marginalize(α::Diagram, v::Int, ⊕)::Diagram = is_term(α) ? Diagram(α.value ⊕ α.value) : reduce!(marginalize_step(α, v, ⊕))
export marginalize
function marginalize_step(α::Diagram, v::Int, ⊕)::Diagram
  if α.index == v return apply(α.low, α.high, ⊕) end
  if is_term(α) return Diagram(α.value ⊕ α.value) end
  l, h = α.low, α.high
  return Diagram(α.index, marginalize_step(l, v, ⊕), marginalize_step(h, v, ⊕))
end

"Returns all variables in this formula as a Vector{Int}."
@inline scope(α::Diagram)::Vector{Int} = collect(scopeset(α))
export scope

"Returns all variables in this formula as a Set{Int}."
function scopeset(α::Diagram)::Set{Int}
  if is_term(α) return Set{Int}() end
  if is_var(α) return Set{Int}(α.index) end
  Sc = Set{Int}()
  foreach(function(v::Diagram)
            if !is_term(v) push!(Sc, v.index) end
          end, α)
  return Sc
end
export scopeset

"Returns whether the formula (i.e. BDD) mentions a variable."
function mentions(α::Diagram, x::Union{Int32, Int64})::Bool
  V = Set{UInt64}(shallowhash(α))
  Q = Diagram[α]
  while !isempty(Q)
    v = pop!(Q)
    if !is_term(v)
      if v.index == x return true end
      l, h = v.low, v.high
      p, q = objectid(l), objectid(h)
      if q ∉ V push!(Q, h); push!(V, q) end
      if p ∉ V push!(Q, l); push!(V, p) end
    end
  end
  return false
end
function mentions(α::Diagram, X::Union{Vector{Int32}, Vector{Int64}})::Bool
  M = Set{Int}(X)
  V = Set{UInt64}(shallowhash(α))
  Q = Diagram[α]
  while !isempty(Q)
    v = pop!(Q)
    if !is_term(v)
      if v.index ∈ M return true end
      l, h = v.low, v.high
      p, q = objectid(l), objectid(h)
      if q ∉ V push!(Q, h); push!(V, q) end
      if p ∉ V push!(Q, l); push!(V, p) end
    end
  end
  return false
end
export mentions
@inline Base.:∈(x::Union{Int32, Int64}, α::Diagram)::Bool = mentions(α, x)
@inline Base.:∉(x::Union{Int32, Int64}, α::Diagram)::Bool = !mentions(α, x)
@inline Base.:∈(X::Union{Vector{Int32}, Vector{Int64}}, α::Diagram)::Bool = mentions(α, X)
@inline Base.:∉(X::Union{Vector{Int32}, Vector{Int64}}, α::Diagram)::Bool = !mentions(α, X)

"Assumes ϕ is a full conjunction of literals. Returns ϕ as a zero-one vector and its scope."
function lit_vec(α::Diagram)::Tuple{BitVector, Vector{Int}}
  X = BitVector()
  S = Vector{Int}()
  Q = Diagram[α]
  # BDDs guarantee variables are top-down increasing.
  while !isempty(Q)
    v = pop!(Q)
    if !is_term(v)
      push!(S, v.index)
      push!(X, is_⊥(v.low) ? true : false)
      if !is_term(v.low) push!(Q, v.low) end
      if !is_term(v.high) push!(Q, v.high) end
    end
  end
  return X, S
end
export lit_vec

"Returns α as an Int32 literal. Assumes α is a leaf node."
@inline to_lit(α::Diagram)::Int32 = Int32(is_⊥(α.low) ? α.index : -α.index)
export to_lit

"""Translates a cardinality constraint in normal pseudo-boolean constraint form into a BDD.

Since cardinality constraints correspond to having coefficients set to one, we ignore the C's.

Argument L corresponds to the vector of literals to be chosen from; b is how many literals in L are
selected.

See Eén and Sörensson 2006."""
@inline function from_npbc(L::Vector{Int}, b::Int)::Diagram
  return reduce!(from_npbc_step(L, b, length(L), 0, Dict{Tuple{Int, Int}, Diagram}(),
                                Diagram(false), Diagram(true)))
end
function from_npbc_step(L::Vector{Int}, b::Int, n::Int, s::Int, M::Dict{Tuple{Int, Int}, Diagram},
                        reuse_⊥::Diagram, reuse_⊤::Diagram)::Diagram
  if s >= b return reuse_⊤
  elseif s + n < b return reuse_⊥ end
  k = (n, s)
  if !haskey(M, k)
    v = L[n]
    positive = v > 0
    if positive
      h_s, l_s = s+1, s
    else
      h_s, l_s = s, s+1
      v = -v
    end
    m = n-1
    h = from_npbc_step(L, b, m, h_s, M, reuse_⊥, reuse_⊤)
    l = from_npbc_step(L, b, m, l_s, M, reuse_⊥, reuse_⊤)
    M[k] = Diagram(v, l, h)
  end
  return M[k]
end

"Constructs a BDD mapping to true if at least n literals in L are in the input; otherwise false."
@inline atleast!(n::Int, L::Vector{Int})::Diagram = from_npbc(sort!(L, by=x->abs(x), rev=true), n)
"Constructs a BDD mapping to true if at least n literals in L are in the input; otherwise false."
@inline atleast(n::Int, L::Vector{Int})::Diagram = atleast!(n, copy(L))
"Constructs a BDD mapping to true if at most n literals in L are in the input; otherwise false."
@inline atmost!(n::Int, L::Vector{Int})::Diagram = (m = length(L); L .= -L; from_npbc(sort!(L, by=x->abs(x), rev=true), m-n))
"Constructs a BDD mapping to true if at most n literals in L are in the input; otherwise false."
@inline atmost(n::Int, L::Vector{Int})::Diagram = atmost!(n, copy(L))
"Constructs a BDD mapping to true if exactly n literals in L are in the input; otherwise false."
@inline exactly!(n::Int, L::Vector{Int})::Diagram = (α = from_npbc(sort!(L, by=x->abs(x), rev=true), n); β = from_npbc(L .= -L, length(L)-n); α ∧ β)
"Constructs a BDD mapping to true if exactly n literals in L are in the input; otherwise false."
@inline exactly(n::Int, L::Vector{Int})::Diagram = exactly!(n, copy(L))
export atleast, atmost, exactly, atleast!, atmost!, exactly!

"Returns the number of nodes in the BDD graph."
@inline Base.size(α::Diagram)::Int = (n = 0; foreach(x -> n += 1, α); n)

end # module