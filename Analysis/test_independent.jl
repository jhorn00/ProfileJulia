using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.Graphs
using Catlab.Graphics
using Catlab.Graphics.Graphviz
using Colors


using Catlab.CategoricalAlgebra.CSets
@present SchemaGraph(FreeSchema) begin
    V::Ob
    E::Ob
    src::Hom(E, V)
    tgt::Hom(E, V)
end
@acset_type Graph(SchemaGraph, index = [:src, :tgt])

g = Graph()
add_parts!(g, :V, 3)