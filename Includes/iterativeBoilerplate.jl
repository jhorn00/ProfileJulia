# This file aims to replace the massive block of "using" or function definitions
# at the top of each file.
using BenchmarkTools
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors
using Plots
using Profile, PProf
using TimerOutputs

draw(g) = to_graphviz(g, node_labels=true, edge_labels=true)
GraphvizGraphs.to_graphviz(f::ACSetTransformation; kw...) =
    to_graphviz(GraphvizGraphs.to_graphviz_property_graph(f; kw...))

function GraphvizGraphs.to_graphviz_property_graph(f::ACSetTransformation; kw...)
    pg = GraphvizGraphs.to_graphviz_property_graph(dom(f); kw...)
    vcolors = hex.(range(colorant"#0021A5", stop=colorant"#FA4616", length=nparts(codom(f), :V)))
    ecolors = hex.(range(colorant"#6C9AC3", stop=colorant"#E28F41", length=nparts(codom(f), :E)))
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
include("graph_bank.jl")
include("autoplot.jl")

# homomorphisms imports
import Catlab.CategoricalAlgebra.CSets: BacktrackingState, find_mrv_elem, BacktrackingSearch
import Catlab.CategoricalAlgebra.CSets: assign_elem!, can_assign_elem, unassign_elem!

# backtracking imports
import Catlab.Theories: SchemaDescType

numSamples = 500
BenchmarkTools.DEFAULT_PARAMETERS.samples = numSamples

const to = TimerOutput()



################################### Run the above code ###################################