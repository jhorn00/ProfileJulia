using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
using TimerOutputs
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
include("autoplot.jl")
include("graph_bank.jl")

# this one actually runs
import Catlab.CategoricalAlgebra.CSets: homomorphisms
import Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra.CSets: map_components


################################### Run the above code ###################################




# necessary structs

# struct SchemaDescType{obs,homs,attrtypes,attrs,doms,codoms}
# end



# struct BacktrackingState{S <: SchemaDescType,
#     Assign <: NamedTuple, PartialAssign <: NamedTuple,
#     Dom <: StructACSet{S}, Codom <: StructACSet{S}}
#   """ The current assignment, a partially-defined homomorphism of ACSets. """
#   assignment::Assign
#   """ Depth in search tree at which assignments were made. """
#   assignment_depth::Assign
#   """ Inverse assignment for monic components or if finding a monomorphism. """
#   inv_assignment::PartialAssign
#   """ Domain ACSet: the "variables" in the CSP. """
#   dom::Dom
#   """ Codomain ACSet: the "values" in the CSP. """
#   codom::Codom
# end









# timers to profile functions
const to = TimerOutput()

# function for homomorphism between two graphs - it was obvious how this would breakdown
function homomorphism(X::StructACSet, Y::StructACSet; kw...)
    @timeit to "Homomorphism(): result initilialization" result = nothing
    @timeit to "Homomorphism(): homs calls" homomorphisms(X, Y; kw...) do α
      @timeit to "Homomorphism(): result assignment" result = α; return true
    end
    result
  end


# it uses two homomorphisms functions
function homomorphisms(X::StructACSet{S}, Y::StructACSet{S};kw...) where {S}
    @timeit to "Homs(): results acset transformation" results = ACSetTransformation{S}[]
    homomorphisms(X, Y; kw...) do α
        @timeit to "Homs(): push" push!(results, map_components(deepcopy, α)); return false
    end
    results
end
@timeit to "Homs(): second homs function" homomorphisms(f, X::StructACSet, Y::StructACSet;monic=false, iso=false, initial=(;)) = @timeit to "Homs(): backtrack" backtracking_search(f, X, Y, monic=monic, iso=iso, initial=initial)


# determining which homs function the graphs use with homomorphism
h1 = homomorphism(line_two, directional_box)
h2 = homomorphism(line_four, directional_box)
h3 = homomorphism(line_six, directional_box)
h4 = homomorphism(line_eight, directional_box)

h1 = homomorphism(line_two, directional_2x2)
h2 = homomorphism(line_four, directional_2x2)
h3 = homomorphism(line_six, directional_2x2)
h4 = homomorphism(line_eight, directional_2x2)

h1 = homomorphism(a_sparse_from, a_sparse_to)
h2 = homomorphism(a_sparse_to, a_sparse_from)
h3 = homomorphism(a_sparse_from2, a_sparse_to2)
h4 = homomorphism(a_sparse_to2, a_sparse_from2)

h1 = homomorphism(a_sparse_from3, a_sparse_to3)
h2 = homomorphism(a_sparse_to3, a_sparse_from3)
h3 = homomorphism(a_sparse_from4, a_sparse_to4)
h4 = homomorphism(a_sparse_to4, a_sparse_from4)

show(to)

# homs
h1 = homomorphisms(line_two, directional_box)
h2 = homomorphisms(line_four, directional_box)
h3 = homomorphisms(line_six, directional_box)
h4 = homomorphisms(line_eight, directional_box)

h1 = homomorphisms(line_two, directional_2x2)
h2 = homomorphisms(line_four, directional_2x2)
h3 = homomorphisms(line_six, directional_2x2)
h4 = homomorphisms(line_eight, directional_2x2)

h1 = homomorphisms(a_sparse_from, a_sparse_to)
h2 = homomorphisms(a_sparse_to, a_sparse_from)
h3 = homomorphisms(a_sparse_from2, a_sparse_to2)
h4 = homomorphisms(a_sparse_to2, a_sparse_from2)

h1 = homomorphisms(a_sparse_from3, a_sparse_to3)
h2 = homomorphisms(a_sparse_to3, a_sparse_from3)
h3 = homomorphisms(a_sparse_from4, a_sparse_to4)
h4 = homomorphisms(a_sparse_to4, a_sparse_from4)

# The calling homomorphisms on two graphs appears to make calls to both
# homs functions equally. The homomorphism function between two graphs
# appears to call the second function exclusively.

# Unsurprisingly the backtracking_search function consumes almost the entirety
# of the function runtime. Further analysis on that will be conducted below.
show(to)

