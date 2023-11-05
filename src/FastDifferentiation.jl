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

const INVARIANTS = true

"""
    @invariant ex msgs...

This macro is used to create invariant test code that is dependent on the global constant `INVARIANTS`. If `INVARIANTS` is false then the test code will not be inserted into the program and there will be no run time overhead. If `INVARIANTS` is true then the code will be inserted. Code that tests invariants tends to increase run time substantially so only set `INVARIANTS` true when you are debugging or testing."""
macro invariant(ex, msgs...)
    if INVARIANTS
        return :(@assert $(esc(ex)) $(esc(msgs)))
    end
end




RuntimeGeneratedFunctions.init(@__MODULE__)

const DefaultNodeIndexType = Int64

include("Methods.jl")
include("Utilities.jl")
include("BitVectorFunctions.jl")
include("ExpressionGraph.jl")

#these definitions must come after ExpressionGraph.jl include because they depend on Node which is defined in ExpressionGraph.jl
RUN_GRAPH_VERIFICATION = true #this should be false during normal use. Only want to turn it on when you suspect a derivative is being computed incorrectly, or when debugging.
GLOBAL_JACOBIAN::Matrix{Node} = Matrix{Node}(undef, 0, 0) #only used for debugging.
GLOBAL_VARIABLES::Vector{Node} = Node[] #only used for debugging.
GLOBAL_INPUT::Vector{Float64} = Float64[] #only used for debugging.

set_checks(a::Bool) = global RUN_GRAPH_VERIFICATION = a
export set_checks

include("PathEdge.jl")
include("DerivativeGraph.jl")
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
