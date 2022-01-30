# Testing graph performance in the graphs.jl documantation

##########################################################
# The below lines are required to run.                   #
##########################################################
using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
#import Catlab.Graphics.Graphviz: to_graphviz, to_graphviz_property_graph

using Colors
draw(g) = to_graphviz(g, node_labels = true, edge_labels = true)

GraphvizGraphs.to_graphviz(f::ACSetTransformation; kw...) =
    to_graphviz(GraphvizGraphs.to_graphviz_property_graph(f; kw...))

function GraphvizGraphs.to_graphviz_property_graph(f::ACSetTransformation; kw...)
    pg = GraphvizGraphs.to_graphviz_property_graph(dom(f); kw...)
    vcolors = hex.(range(colorant"#0021A5", stop = colorant"#FA4616", length = nparts(codom(f), :V)))
    ecolors = hex.(range(colorant"#6C9AC3", stop = colorant"#E28F41", length = nparts(codom(f), :E)))
    hex.(colormap("Oranges", nparts(codom(f), :V)))
    for v in vertices(dom(f))
        fv = f[:V](v)
        set_vprops!(pg, v, Dict(:color => "#$(vcolors[fv])"))
    end
    for e in edges(dom(f))
        fe = f[:E](e)
        set_eprops!(pg, e, Dict(:color => "#$(ecolors[fe])"))
    end
    pg
end
##########################################################

#====================James Horn Part======================#
# Theory Graph is a premade simple graph
to_graphviz(Catlab.Graphs.BasicGraphs.TheoryGraph)

# Basic graph with one edge
e = @acset Graphs.Graph begin
    V = 2
    E = 1
    src = [1]
    tgt = [2]
end

# Wedge graph
w = @acset Graphs.Graph begin
    V = 3
    E = 2
    src = [1, 3]
    tgt = [2, 2]
end

#draw function testing
sim_gen_draw_bench_e = @benchmark draw($e)
sim_gen_draw_bench_w = @benchmark draw($w)

# this can be used to easily compare performance (values other than median can be used here)
ratio(median(sim_gen_draw_bench_e), median(sim))
# for example:
ratio(minimum(sim_gen_draw_bench_e), minimum(sim_gen_draw_bench_w))
ratio(maximum(sim_gen_draw_bench_e), maximum(sim_gen_draw_bench_w))
# basically, it should work on anpy part of a BenchmarkTools.Trial type
# naturally we are probably going to target a median values, but you already know that

# this can be used to test possible improvements
judge(median(sim_gen_draw_bench_e), median(sim_gen_draw_bench_w))
# We can see that for this simple graph example, drawing one more edge and one more vertex causes a performance
# loss of ~16-19%. That's not to say we should concentrate efforts on Graphviz, it's just an example.
# I would like to note that the time has reported as invariant in some cases. The memory is consistent.
#=========================================================#

# Original Doc Info - These seem unnecessary to benchmark
##########################################################
# The CSet API generalizes the traditional Graph API
parts(w, :V)  # vertex set
parts(w, :E) # edge set
w[:src] # source map
w[:tgt] # target map
incident(w, 1, :src) # edges out of vertex 1
incident(w, 2, :tgt) # edges into vertex 2
w[incident(w, 2, :tgt), :src] # vertices that are the source of edges whose target is vertex 2
w[incident(w, 1, :src), :tgt] # vertices that are the target of edges whose src is vertex 1
##########################################################

# # Graph Homomorphisms
# We can construct some graph homomorphisms between our two graphs.
# What data do we need to specify?

#====================James Horn Part======================#
# ACSetTransformation
ϕ = ACSetTransformation(e, w, E = [1], V = [1, 2])
actrans_A = @benchmark ACSetTransformation($e, $w, E = [1], V = [1, 2])
#is_natural
is_natural(ϕ)
is_nat_A = @benchmark is_natural($ϕ)
# The ACSetTransformation constructor does not automatically validate that the naturality squares commute!
ϕᵦ = ACSetTransformation(e, w, E = [1], V = [3, 2])
actrans_B = @benchmark ACSetTransformation($e, $w, E = [1], V = [3, 2])
is_natural(ϕᵦ)
is_nat_B = @benchmark is_natural($ϕᵦ)
# Our ϕᵦ in't natural because the edge map e₁ ↦ e₁ is not consistent with our vertex map, which sends v₁ ↦ v₃ and v₂ ↦ v₂. We can fix this by sending e₁ to e₂
ϕᵦ′ = ACSetTransformation(e, w, E = [2], V = [3, 2])
actrans_B_prime = @benchmark ACSetTransformation($e, $w, E = [2], V = [3, 2])
is_natural(ϕᵦ′)
is_nat_B_prime = @benchmark is_natural($ϕᵦ′)

# Comparing B and B' since it is a more direct comparison.
# ACSetTransformation shows no real difference, which was expected.
# If it were to be judged the results would report invariance.
ratio(median(actrans_B), median(actrans_B_prime))
# The following has a significant difference in performance, more so to memory and allocations than to time.
# The time of the first is_natural run is still 3/4 that of the second. That is obviously because false
# gives an early termination through short-circuits.
#=
function is_natural(α::ACSetTransformation{S}) where {S}
  X, Y = dom(α), codom(α)
  for (f, c, d) in zip(hom(S), dom(S), codom(S))
    Xf, Yf, α_c, α_d = subpart(X,f), subpart(Y,f), α[c], α[d]
    all(Yf[α_c(i)] == α_d(Xf[i]) for i in eachindex(Xf)) || return false
  end
  for (f, c) in zip(attr(S), adom(S))
    Xf, Yf, α_c = subpart(X,f), subpart(Y,f), α[c]
    all(Yf[α_c(i)] == Xf[i] for i in eachindex(Xf)) || return false
  end
  return true
end
=#
ratio(median(is_nat_B), median(is_nat_B_prime))
# At the moment it is unclear just what improvements could be made to this performance.
# From my understanding I don't think much is possible here and an analysis of the function
# already exists on the Catlab documantation. I would like to note that the documentation (below)
# does not reference the second for loop, nor does the code snippet.
#=========================================================#


# Original Doc Info - These are unnecessary to benchmark
##########################################################
# So how does Catlab store the data of the natural transformation? 
# the domain
ϕ.dom
# the codomain
ϕ.codom
# the components
ϕ.components
# you can see the components using standard indexing notation with the object names. Notice that while CSets are indexed by morphisms, natural transformations are indexed by objects.
ϕ[:V]
ϕ[:E]
# We can check the  naturality squares ourselves
# The sources are preserved: `src ⋅ ϕᵥ == ϕₑ ⋅ src`
ϕ[:V](dom(ϕ)[:, :src]) == codom(ϕ)[collect(ϕ[:E]), :src]
# The targets are preserved: `tgt ⋅ ϕᵥ == ϕₑ ⋅ tgt`
ϕ[:V](dom(ϕ)[:, :tgt]) == codom(ϕ)[collect(ϕ[:E]), :tgt]

# This approach generalizes to the following: 
#
# ```julia
# function is_natural(α::ACSetTransformation{S}) where {S}
#    X, Y = dom(α), codom(α)
#    for (f, c, d) in zip(hom(S), dom(S), codom(S))
#      Xf, Yf, α_c, α_d = subpart(X,f), subpart(Y,f), α[c], α[d]
#      all(Yf[α_c(i)] == α_d(Xf[i]) for i in eachindex(Xf)) || return false
#    end
#    return true
# end
# ```
#
# Notice how we iterate over the homs in the schema category S `(f, c, d) in zip(hom(S), dom(S), codom(S))` We get one universally quantified equation `all(Yf[α_c(i)] == α_d(Xf[i]) for i in eachindex(Xf))` for each morphism in the indexing category
##########################################################

# ## Finding Homomorphisms Automatically
# As you saw in the previous exercise, constructing a natural transformation can be quite tedious. We want computers to automate tedious things for us. So we use an algorithm to enumerate all the homomorphisms between two CSets.
# CSet homomorphisms f:A→B are ways of finding a part of B that is shaped like A. You can view this as pattern matching. The graph A is the pattern and the graph B is the data. A morphism f:A→B is a collection of vertices and edges in B that is shaped like A. Note that you can ask Catlab to enforce constraints on the homomorphisms it will find including computing monic (injective) morphisms by passing the keyword `monic=true`. A monic morphism into B is a subobject of B.  You can pass `iso=true` to get isomorphisms.

#====================James Horn Part======================#
# The below functions appear to have undergone efficiency consideration already.
# The only issues they may pose would be related to recursion (specifically in homomorphims()).
#=========================================================#

# Original Doc Info - Not benchmarked but can be
##########################################################

# Graph creation
t = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 2, 1]
    tgt = [2, 3, 3]
end
draw(t)

T = @acset Graphs.Graph begin
    V = 6
    E = 9
    src = [1, 2, 1, 3, 1, 5, 2, 2, 4]
    tgt = [2, 3, 3, 4, 4, 6, 5, 6, 6]
end
draw(T)

# The simplest pattern in a graph is just a single edge and each homomorphism ϕ:e→G is a single edge in G. 
length(homomorphisms(e, T, monic = true)) == nparts(T, :E) # number of edges
length(homomorphisms(t, T))
# We can define this helper function to print out all the homomorphisms between graphs. Because all our graphs are simple, we only need to look at the vertex components.
graphhoms(g, h) = begin
    map(homomorphisms(g, h)) do ϕ
        collect(ϕ[:V])
    end
end

graphhoms(t, T)
# Homs ϕ:t→T are little triangles in T, but homs ϕ:T→t are colorings of T with 3 colors. The fact that there are edges in t that are missing, means that it provides constraints on what graphs have morphisms into it. For example, there are no morphisms T→t.
graphhoms(T, t)
# The reason we don't have a morphism into t is vertices 2,3,4,5 aren't arranged into a triangle. We can relax those constraints by adding loops to the codomain. Loops in the codomain allow you to merge adjacent vertices when you construct the homomorphism. 
add_loops!(g) = add_parts!(g, :E, nparts(g, :V), src = parts(g, :V), tgt = parts(g, :V))
add_loops(g) = begin
    h = copy(g)
    add_loops!(h)
    return h
end
draw(add_loops(t))

# Once we add loops, then we have morphisms.
length(homomorphisms(T, add_loops(t)))

# ## Bipartite Graphs
# Many computer science problems involve graphs that have two types of vertices. For example, when matching students to classes, you might represent the students as one type of vertex and the classes as another type of vertex. Then the edges (s,c) represent "student s is enrolled in class c". In this scenario there can be no edges from a class vertex to another class vertex, or from a student vertex to a student vertex. Graphs for which there exists such a classification are called bipartite graphs. In Category Theory, we shift from thinking about graphs with properties to graph homomorphisms that witness that property and think of bipartitioned graphs.

# First we construct a bipartite graph:
sq = apex(product(add_loops(e), add_loops(e)))
rem_parts!(sq, :E, [1, 5, 6, 8, 9])
draw(sq)

# We will use the symmetric edge graph to identify the bipartitions of this graph. 
esym = @acset Graphs.Graph begin
    V = 2
    E = 2
    src = [1, 2]
    tgt = [2, 1]
end

draw(id(esym))
# There are two ways to bipartition sq.
graphhoms(sq, esym)
# This comes from the fact that esym has 2 automorphisms!
graphhoms(esym, esym)
# the first coloring
draw(homomorphisms(sq, esym)[1])
# but we can also swap the roles of the colors
draw(homomorphisms(sq, esym)[2])
# We can generalize the notion of Bipartite graph to any number of parts. I like to call Kₖ the k-coloring classifier because homomorphims into α:G → Kₖ are k-colorings of G.
clique(k::Int) = begin
    Kₖ = Graphs.Graph(k)
    for i in 1:k
        for j in 1:k
            if j ≠ i
                add_parts!(Kₖ, :E, 1, src = i, tgt = j)
            end
        end
    end
    return Kₖ
end
K₃ = clique(3)
draw(id(K₃))
# Our graph T is not 2-colorable,
length(homomorphisms(T, esym))
# but we can use 3 colors to color T.
draw(homomorphism(T, K₃))
# ## Homomorphisms in [C, Set] are like Types
# Any graph can play the role of the codomain. If you pick a graph that is incomplete, you get a more constrained notion of coloring where there are color combinations that are forbidden.
triloop = @acset Graphs.Graph begin
    V = 3
    E = 3
    src = [1, 2, 3]
    tgt = [2, 3, 1]
end
draw(id(triloop))
# With this graph, we can pick out directed 3-cycles in a graph like T2,
T2 = @acset Graphs.Graph begin
    V = 6
    E = 6
    src = [1, 2, 3, 4, 5, 6]
    tgt = [2, 3, 1, 5, 6, 4]
end
graphhoms(T2, triloop)
# and we can draw those cyclic roles with colors
draw(homomorphisms(T2, triloop)[1])
T3 = @acset Graphs.Graph begin
    V = 6
    E = 7
    src = [1, 2, 3, 4, 5, 6, 2]
    tgt = [2, 3, 1, 5, 6, 4, 4]
end
graphhoms(T3, triloop)
# Using the colors as shown:
draw(id(triloop))
# We can see our coloring of T3:
draw(homomorphisms(T3, triloop)[1])
##########################################################