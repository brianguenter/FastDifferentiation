module FastDifferentiation

# using TermInterface
using StaticArrays
using SpecialFunctions
using NaNMath
# using Statistics
using RuntimeGeneratedFunctions
import Base: iterate
using UUIDs
using SparseArrays
using DataStructures


module AutomaticDifferentiation
struct NoDeriv
end
export NoDeriv
end #module


RuntimeGeneratedFunctions.init(@__MODULE__)

const DefaultNodeIndexType = Int64

include("Methods.jl")
include("Utilities.jl")
include("BitVectorFunctions.jl")
include("ExpressionGraph.jl")
include("PathEdge.jl")
include("DerivativeGraph.jl")

#these definitions must come after DerivativeGraph.jl and ExpressionGraph.jl include because they depend on Node which is defined in ExpressionGraph.jl and DerivativeGraph
RUN_GRAPH_VERIFICATION = false #this should be false during normal use. Only want to turn it on when you suspect a derivative is being computed incorrectly, or when debugging.
GLOBAL_JACOBIAN::Matrix{Node} = Matrix{Node}(undef, 0, 0) #only used for debugging.
GLOBAL_VARIABLES::Vector{Node} = Node[] #only used for debugging.
GLOBAL_INPUT::Vector{Float64} = Float64[] #only used for debugging.

function set_checks(graph::DerivativeGraph)
    global RUN_GRAPH_VERIFICATION = true
    global GLOBAL_JACOBIAN = reverse_AD(graph)
    global GLOBAL_VARIABLES = variables(graph)
    global GLOBAL_INPUT = rand(domain_dimension(graph))
end

include("Reverse.jl")
include("GraphProcessing.jl")
include("FactorableSubgraph.jl")
include("Factoring.jl")
include("Jacobian.jl")
include("CodeGeneration.jl")


# FastDifferentiationVisualizationExt overloads them
function make_dot_file end
function draw_dot end
function write_dot end


end # module
