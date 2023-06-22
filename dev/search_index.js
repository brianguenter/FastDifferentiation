var documenterSearchIndex = {"docs":
[{"location":"futurework/#Future-Work","page":"-","title":"Future Work","text":"","category":"section"},{"location":"futurework/","page":"-","title":"-","text":"The top priority work item is reducing memory allocations and improving performance of the preprocessing step.","category":"page"},{"location":"futurework/","page":"-","title":"-","text":"The FD algorithm is fast enough to preprocess expression graphs with ≈10⁵ operations in approximately 1 minute on a modern laptop. This is a one time step to generate compiled derivative functions which, of course, take far less than 1 minute to execute. Preprocessing time scales non-linearly with expression size so smaller graphs take much less time.","category":"page"},{"location":"futurework/","page":"-","title":"-","text":"However, LLVM compile time can be significant at this scale. For expressions this size and larger DynamicExpressions.jl might be a better tradeoff between compile and execution time. This would be especially useful when your function is changing frequently so compilation overhead cannot be amortized across many derivative evaluations.","category":"page"},{"location":"futurework/","page":"-","title":"-","text":"FD cannot differentiate expressions with conditionals involving FD variables. The algorithm can be extended to allow this but symbolic processing can scale exponentially with the nesting depth of conditionals. For small nesting depths this might be acceptable so a future version of FD might support limited nested conditionals. ","category":"page"},{"location":"futurework/","page":"-","title":"-","text":"However, a better approach might be to use FD as a processing step in a tracing JIT compiler, applying FD to the basic blocks detected and compiled by the JIT. These basic blocks do not have branches. Many programs could be differentiated competely automatically by this method. I'm not a compiler expert so it is unlikely I will do this by myself. But contact me if you are a compiler expert and want a cool project to work on.","category":"page"},{"location":"benchmarks/","page":"Benchmarks","title":"Benchmarks","text":"Coming soon!","category":"page"},{"location":"api/","page":"API","title":"API","text":"Modules = [FastDifferentiation]\nPrivate = false\nOrder = [:function]","category":"page"},{"location":"api/#FastDifferentiation.clear_cache-Tuple{}","page":"API","title":"FastDifferentiation.clear_cache","text":"Clears the global expression cache. To maximize efficiency of expressions the differentation system automatically eliminates common subexpressions by checking for their existence in the global expression cache. Over time this cache can become arbitrarily large. Best practice is to clear the cache before you start defining expressions, define your expressions and then clear the cache.\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.derivative-Union{Tuple{T}, Tuple{Matrix{<:FastDifferentiation.Node}, Vararg{T}}} where T<:FastDifferentiation.Node","page":"API","title":"FastDifferentiation.derivative","text":"computes ∂A/(∂variables[1],...,∂variables[n]). Repeated differentiation rather than computing different columns of the Jacobian. Example:\n\n\njulia> A = [t t^2;3t^2 5]  \n2×2 Matrix{Node}:\n t              (t ^ 2)\n (3 * (t ^ 2))  5\n\njulia> derivative(A,t)  \n2×2 Matrix{Node}:\n 1.0      (2 * t)\n (6 * t)  0.0\n\njulia> derivative(A,t,t)  \n2×2 Matrix{Node{T, 0} where T}:\n 0.0  2\n 6    0.0\n\n\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.hessian-Tuple{FastDifferentiation.DerivativeGraph, Any}","page":"API","title":"FastDifferentiation.hessian","text":"Computes the full symbolic Hessian matrix\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.hessian-Union{Tuple{S}, Tuple{FastDifferentiation.Node, AbstractVector{S}}} where S<:FastDifferentiation.Node","page":"API","title":"FastDifferentiation.hessian","text":"Computes the full symbolic Hessian matrix\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.hessian_times_v-Union{Tuple{S}, Tuple{T}, Tuple{T, AbstractVector{S}}} where {T<:FastDifferentiation.Node, S<:FastDifferentiation.Node}","page":"API","title":"FastDifferentiation.hessian_times_v","text":"Computes Hessian times a vector v without forming the Hessian matrix. Useful when the Hessian would be impractically large.\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.jacobian-Union{Tuple{S}, Tuple{T}, Tuple{AbstractVector{T}, AbstractVector{S}}} where {T<:FastDifferentiation.Node, S<:FastDifferentiation.Node}","page":"API","title":"FastDifferentiation.jacobian","text":"Jacobian matrix of the n element function defined by terms. Each term element is a Node expression graph. Only the columns of the Jacobian corresponsing to the elements of partial_variables will be computed and the partial columns in the Jacobian matrix will be in the order specified by partial_variables. Examples:\n\n\njulia> @variables x y\n\njulia> jacobian([x*y,y*x],[x,y])\n2×2 Matrix{Node}:\n y  x\n y  x\n\njulia> jacobian([x*y,y*x],[y,x])\n2×2 Matrix{Node}:\n x  y\n x  y\n\njulia> jacobian([x*y,y*x],[x])\n2×1 Matrix{Node}:\n y\n y\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.jacobian_times_v-Union{Tuple{S}, Tuple{T}, Tuple{AbstractVector{T}, AbstractVector{S}}} where {T<:FastDifferentiation.Node, S<:FastDifferentiation.Node}","page":"API","title":"FastDifferentiation.jacobian_times_v","text":"Returns a vector of Node, where each element in the vector is the symbolic form of Jv. Also returnsv_vectora vector of thevvariables. This is useful if you want to generate a function to evaluateJvand you want to separate the inputs to the function and thev` variables.\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.jacobian_transpose_v-Union{Tuple{S}, Tuple{T}, Tuple{AbstractVector{T}, AbstractVector{S}}} where {T<:FastDifferentiation.Node, S<:FastDifferentiation.Node}","page":"API","title":"FastDifferentiation.jacobian_transpose_v","text":"Returns a vector of Node, where each element in the vector is the symbolic form of Jᵀv. Also returns v_vector a vector of the v variables. This is useful if you want to generate a function to evaluate Jᵀv and you want to separate the inputs to the function and the v variables.\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.sparse_jacobian-Union{Tuple{S}, Tuple{T}, Tuple{AbstractVector{T}, AbstractVector{S}}} where {T<:FastDifferentiation.Node, S<:FastDifferentiation.Node}","page":"API","title":"FastDifferentiation.sparse_jacobian","text":"Returns a sparse array containing the Jacobian of the function defined by terms\n\n\n\n\n\n","category":"method"},{"location":"api/#FastDifferentiation.sparsity-Tuple{FastDifferentiation.DerivativeGraph}","page":"API","title":"FastDifferentiation.sparsity","text":"Computes sparsity of Jacobian matrix = nonzeroentries/total_entries.\n\n\n\n\n\n","category":"method"},{"location":"symbolicprocessing/#Symbolic-Processing","page":"Symbolic processing","title":"Symbolic Processing","text":"","category":"section"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"Because FD can generate true symbolic derivatives it can easily be used in conjunction with Symbolics.jl using the package FDConversion.jl (still under development).","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"A rule of thumb is that if your function is small (a few hundred operations or less) or tree like (where each node in the expression graph has one parent on average) then Symbolics.jl may outperform or equal FD. For more complex functions with many common subexpressions FD may substantially outperform Symbolics.jl.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"Take these benchmarks with a large grain of salt since there are so few of them. Whether your function will have this kind of performance improvement relative to Symbolics.jl is hard to predict until the benchmark set gets much bigger.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"These benchmarks should give you a sense of what performance you might achieve for symbolic processing. There are three types of benchmarks: Symbolic, MakeFunction, and Exe.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The Symbolic benchmark is the time required to compute just the symbolic form of the derivative. The Symbolic benchmark can be run with simplification turned on or off for Symbolics.jl. If simplification is on then computation time can be extremely long but the resulting expression might be simpler and faster to execute.\nThe MakeFunction benchmark is the time to generate a Julia Expr from an already computed symbolic derivative and to then compile it.\nThe Exe benchmark measures just the time required to execute the compiled function using an in-place matrix.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"All benchmarks show the ratio of time taken by Symbolics.jl to FastDifferentiation.jl. Numbers greater than 1 mean FastDifferentiation is faster.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"All benchmarks were run on an AMD Ryzen 9 7950X 16-Core Processor with 32GB RAM running Windows 11 OS, Julia version 1.9.0.","category":"page"},{"location":"symbolicprocessing/#Chebyshev-polynomial","page":"Symbolic processing","title":"Chebyshev polynomial","text":"","category":"section"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The first example is a recursive function for  the Chebyshev polynomial of order n:","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"@memoize function Chebyshev(n, x)\n    if n == 0\n        return 1\n    elseif n == 1\n        return x\n    else\n        return 2 * (x) * Chebyshev(n - 1, x) - Chebyshev(n - 2, x)\n    end\nend","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The function is memoized so the recursion executes efficiently. ","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The recursive function returns an nth order polynomial in the variable x. The derivative of this polynomial would be order n-1 so a perfect symbolic simplification would result in a function with 2*(n-2) operations. For small values of n Symbolics.jl simplification does fairly well but larger values result in very inefficient expressions.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"Because FD doesn't do sophisticated symbolic simplification it generates a derivative with approximately 2.4x the number of operations in the original recursive expression regardless of n. This is a case where a good hand generated derivative would be more efficient than FD.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The Chebyshev expression graph does not have many nodes even at the largest size tested (graph size increases linearly with Chebyshev order).","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The first set of three benchmarks show results with simplification turned off in Symbolics.jl, followed by a set of three with simplification turned on. Performance is somewhat better in the latter case but still slower than the FD executable. Note that the y axis is logarithmic.","category":"page"},{"location":"symbolicprocessing/#Chebyshev-benchmarks-with-simplification-off","page":"Symbolic processing","title":"Chebyshev benchmarks with simplification off","text":"","category":"section"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"(Image: Symbolic processing, simplify=false)  (Image: MakeFunction, simplify=false)  (Image: Exe, simplify=false)","category":"page"},{"location":"symbolicprocessing/#Chebyshev-benchmarks-with-simplification-on","page":"Symbolic processing","title":"Chebyshev benchmarks with simplification on","text":"","category":"section"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"(Image: MakeFunction, simplify=false)","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"With simplification on performance of the executable derivative function for Symbolics.jl is slightly better than with simplification off. But simplification processing time is longer.","category":"page"},{"location":"symbolicprocessing/#Spherical-Harmonics","page":"Symbolic processing","title":"Spherical Harmonics","text":"","category":"section"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The second example is the spherical harmonics function. This is the expression graph for the spherical harmonic function of order 8: (Image: MakeFunction, simplify=false)","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"@memoize function P(l, m, z)\n    if l == 0 && m == 0\n        return 1.0\n    elseif l == m\n        return (1 - 2m) * P(m - 1, m - 1, z)\n    elseif l == m + 1\n        return (2m + 1) * z * P(m, m, z)\n    else\n        return ((2l - 1) / (l - m) * z * P(l - 1, m, z) - (l + m - 1) / (l - m) * P(l - 2, m, z))\n    end\nend\nexport P\n\n@memoize function S(m, x, y)\n    if m == 0\n        return 0\n    else\n        return x * C(m - 1, x, y) - y * S(m - 1, x, y)\n    end\nend\nexport S\n\n@memoize function C(m, x, y)\n    if m == 0\n        return 1\n    else\n        return x * S(m - 1, x, y) + y * C(m - 1, x, y)\n    end\nend\nexport C\n\nfunction factorial_approximation(x)\n    local n1 = x\n    sqrt(2 * π * n1) * (n1 / ℯ * sqrt(n1 * sinh(1 / n1) + 1 / (810 * n1^6)))^n1\nend\nexport factorial_approximation\n\nfunction compare_factorial_approximation()\n    for n in 1:30\n        println(\"n $n relative error $((factorial(big(n))-factorial_approximation(n))/factorial(big(n)))\")\n    end\nend\nexport compare_factorial_approximation\n\n@memoize function N(l, m)\n    @assert m >= 0\n    if m == 0\n        return sqrt((2l + 1 / (4π)))\n    else\n        # return sqrt((2l+1)/2π * factorial(big(l-m))/factorial(big(l+m)))\n        #use factorial_approximation instead of factorial because the latter does not use Stirlings approximation for large n. Get error for n > 2 unless using BigInt but if use BigInt get lots of rational numbers in symbolic result.\n        return sqrt((2l + 1) / 2π * factorial_approximation(l - m) / factorial_approximation(l + m))\n    end\nend\nexport N\n\n\"\"\"l is the order of the spherical harmonic\"\"\"\n@memoize function Y(l, m, x, y, z)\n    @assert l >= 0\n    @assert abs(m) <= l\n    if m < 0\n        return N(l, abs(m)) * P(l, abs(m), z) * S(abs(m), x, y)\n    else\n        return N(l, m) * P(l, m, z) * C(m, x, y)\n    end\nend\nexport Y\n\nSHFunctions(max_l, x::Node, y::Node, z::Node) = SHFunctions(Vector{Node}(undef, 0), max_l, x, y, z)\nSHFunctions(max_l, x::Symbolics.Num, y::Symbolics.Num, z::Symbolics.Num) = SHFunctions(Vector{Symbolics.Num}(undef, 0), max_l, x, y, z)\n\nfunction SHFunctions(shfunc, max_l, x, y, z)\n    for l in 0:max_l-1\n        for m in -l:l\n            push!(shfunc, Y(l, m, x, y, z))\n        end\n    end\n\n    return shfunc\nend\nexport SHFunctions\n\nfunction spherical_harmonics(::JuliaSymbolics, model_size)\n    Symbolics.@variables x y z\n    return SHFunctions(model_size, x, y, z), [x, y, z]\nend\n\nfunction spherical_harmonics(::FastSymbolic, model_size, x, y, z)\n    graph = DerivativeGraph(SHFunctions(model_size, x, y, z))\n    return graph\nend\n\nfunction spherical_harmonics(package::FastSymbolic, model_size)\n    FD.@variables x, y, z\n    return spherical_harmonics(package, model_size, x, y, z)\nend\nexport spherical_harmonics","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"As was the case for Chebyshev polynomials the number of paths from the roots to the variables is much greater than the number of nodes in the graph. Once again the y axis is logarithmic.","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"(Image: Symbolic processing, simplify=false) (Image: MakeFunction, simplify=false) (Image: Exe, simplify=false)","category":"page"},{"location":"symbolicprocessing/","page":"Symbolic processing","title":"Symbolic processing","text":"The Exe benchmark took many hours to run and was stopped at model size 24 instead of 25 as for the Symbolic and MakeFunction benchmarks.","category":"page"},{"location":"examples/#Examples","page":"Examples","title":"Examples","text":"","category":"section"},{"location":"examples/","page":"Examples","title":"Examples","text":"The first step is to create FD variables which are then passed to the function you want to differentiate. The return value is a graph structure which FD will analyze to generate efficient executables or symbolic expressions.","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"FD uses a global cache for common subexpression elimination so the FD expression preprocessing step is not thread safe. ","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Under ordinary conditions the memory used by the cache won't be an issue. But, if you have a long session where you are creating many complex functions it is possible the cache will use too much memory. If this happens call the function clear_cache after you have completely processed your expression.","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Set up variables:","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"using FastDifferentiation\n\n@variables x y z\n","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Make a vector of variables","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> X = make_variables(:x,3)\n3-element Vector{Node}:\n x1\n x2\n x3","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Make an executable function","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> xy_exe = make_function([x^2*y^2,sqrt(x*y)],[x,y]) #[x,y] vector specifies the order of the arguments to the exe\n...\njulia> xy_exe([1.0,2.0])\n2-element Vector{Float64}:\n 4.0\n 1.4142135623730951","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Compute Hessian:","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"@variables x y z\n\njulia> h_symb = hessian(x^2+y^2+z^2,[x,y,z])\n3×3 Matrix{Node}:\n 2    0.0  0.0\n 0.0  2    0.0\n 0.0  0.0  2\n\njulia> h_symb1 = hessian(x^2*y^2*z^2,[x,y,z])\n3×3 Matrix{FastDifferentiation.Node}:\n (2 * ((z ^ 2) * (y ^ 2)))        (((2 * x) * (2 * y)) * (z ^ 2))  (((2 * x) * (2 * z)) * (y ^ 2))\n (((2 * y) * (2 * x)) * (z ^ 2))  (2 * ((z ^ 2) * (x ^ 2)))        (((2 * y) * (2 * z)) * (x ^ 2))\n (((2 * z) * (2 * x)) * (y ^ 2))  (((2 * z) * (2 * y)) * (x ^ 2))  (2 * ((x ^ 2) * (y ^ 2)))\n\njulia> hexe_1 = make_function(h_symb1,[x,y,z])\n...\njulia> hexe_1([1.0,2.0,3.0])\n3×3 Matrix{Float64}:\n 72.0  72.0  48.0\n 72.0  18.0  24.0\n 48.0  24.0   8.0","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Compute Hv without forming the full Hessian matrix. This is useful if the Hessian is very large","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> @variables x y\ny\n\njulia> f = x^2 * y^2\n((x ^ 2) * (y ^ 2))\n\njulia> hv_fast, v_vec2 = hessian_times_v(f, [x, y])\n...\n\njulia> hv_fast_exe = make_function(hv_fast, [[x, y]; v_vec2]) #need v_vec2 because hv_fast is a function of x,y,v1,v2 and have to specify the order of all inputs to the executable\n...\njulia> hv_fast_exe([1.0,2.0,3.0,4.0]) #first two vector elements are x,y last two are v1,v2\n2-element Vector{Float64}:\n 56.0\n 32.0","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Compute Jacobian:","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> f1 = cos(x) * y\n(cos(x) * y)\n\njulia> f2 = sin(y) * x\n(sin(y) * x)\n\njulia> symb = jacobian([f1, f2], [x, y]) #non-destructive\n2×2 Matrix{Node}:\n (y * -(sin(x)))  cos(x)\n sin(y)           (x * cos(y))","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Create executable to evaluate Jacobian:","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> jac_exe = make_function(symb,[x,y])\n...\njulia> jac_exe([1.0,2.0])\n2×2 Matrix{Float64}:\n -1.68294    0.540302\n  0.909297  -0.416147","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Executable with inplace matrix evaluation to avoid allocation of a matrix for the Jacobian (inplace option available on all executables including Jᵀv,Jv,Hv):","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> jac_exe = make_function(symb,[x,y], in_place=true)\n...\njulia> a = Matrix{Float64}(undef,2,2)\n2×2 Matrix{Float64}:\n 0.0  0.0\n 0.0  6.93532e-310\n\njulia> jac_exe([1.0,2.0],a)\n2×2 Matrix{Float64}:\n -1.68294    0.540302\n  0.909297  -0.416147\n\njulia> a\n2×2 Matrix{Float64}:\n -1.68294    0.540302\n  0.909297  -0.416147","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"For out of place evaluation (matrix created and returned by executable function) input vector and return matrix of executable can be any mix of StaticArray and Vector. If the first argument to make_function is a subtype of StaticArray then the compiled executable will return a StaticArray value. The compiled executable can be called with either an SVector or Vector argument. For small input sizes the SVector should be faster, essentially the same as passing the input as scalar values.","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"For functions with low input and output dimensions the fastest executable will be generated by calling make_function with first argument a subtype of StaticArray and calling the executable with an SVector argument. The usual cautions of StaticArrays apply, that total length of the return value < 100 or so and total length of the input < 100 or so.","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> @variables x y\ny\n\njulia> j = jacobian([x^2 * y^2, cos(x + y), log(x / y)], [x, y]);\n\njulia> j_exe = make_function(j, [x, y]);\n\njulia> @assert typeof(j_exe([1.0, 2.0])) <: Array #return type is Array and input type is Vector\n\njulia> j_exe2 = make_function(SArray{Tuple{3,2}}(j), [x, y]);\n\njulia> @assert typeof(j_exe2(SVector{2}([1.0, 2.0]))) <: StaticArray #return type is StaticArray and input type is SVector. This should be the fastest.","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Compute any subset of the columns of the Jacobian:","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> symb = jacobian([x*y,y*z,x*z],[x,y,z]) #all columns\n3×3 Matrix{Node}:\n y    x    0.0\n 0.0  z    y\n z    0.0  x\n\njulia> symb = jacobian([x*y,y*z,x*z],[x,y]) #first two columns\n3×2 Matrix{Node}:\n y    x\n 0.0  z\n z    0.0\n\njulia> symb = jacobian([x*y,y*z,x*z],[z,y]) #second and third columns, reversed so ∂f/∂z is 1st column of the output, ∂f/∂y the 2nd\n3×2 Matrix{Node}:\n 0.0  x\n y    z\n x    0.0","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Symbolic and executable Jᵀv and Jv (see this paper for applications of this operation).","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> (f1,f2) = cos(x)*y,sin(y)*x\n((cos(x) * y), (sin(y) * x))\n\njulia> jv,vvec = jacobian_times_v([f1,f2],[x,y])\n...\n\njulia> jv_exe = make_function(jv,[[x,y];vvec])\n...\n\njulia> jv_exe([1.0,2.0,3.0,4.0]) #first 2 arguments are x,y values and last two are v vector values\n\n2×1 Matrix{Float64}:\n -2.8876166853748195\n  1.0633049342884753\n\njulia> jTv,rvec = jacobian_transpose_v([f1,f2],[x,y])\n...\n\njulia> jtv_exe = make_function(jTv,[[x,y];rvec])\n...\njulia> jtv_exe([1.0,2.0,3.0,4.0])\n2-element Vector{Float64}:\n -1.4116362015446517\n -0.04368042858415033","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"Convert between FastDifferentiation and Symbolics representations (requires FDConversion package, not released yet[1]):","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"julia> f = x^2+y^2 #Symbolics expression\nx^2 + y^2\n\njulia> Node(f) #convert to FastDifferentiation form\nx^2 + y^2\n\njulia> typeof(ans)\nNode{SymbolicUtils.BasicSymbolic{Real}, 0}\n\njulia> node_exp = x^3/y^4 #FastDifferentiation expression\n((x ^ 3) / (y ^ 4))\n\njulia> to_symbolics(node_exp)\n(x^3) / (y^4)\n\njulia> typeof(ans)\nSymbolics.Num","category":"page"},{"location":"examples/","page":"Examples","title":"Examples","text":"[1]: I am working with the SciML team to see if it is possible to integrate FD differentiation directly into Symbolics.jl.","category":"page"},{"location":"howitworks/#How-it-works","page":"How it works","title":"How it works","text":"","category":"section"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"The FD differentiation algorithm is related to the D* algorithm but is asymptotically faster so it works on much larger expression graphs. The new algorithms used in FD will be described in a soon to be written paper.","category":"page"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"FD transforms the input expression graph into a derivative graph[2], and then factors this graph to generate an efficient expression for the derivative. This is fundamentally different from forward and reverse automatic differentiation. ","category":"page"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"The efficiency of FD comes from analysis of the graph structure of the function rather than sophisticated algebraic simplification rules. By default FD applies only these algebraic simplications[1] to expressions:","category":"page"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"x×0=>0\nx×1=>x\nx/1=>x\nx+0=>x\nc₁×c₂=>c₃ for c₁,c₂,c₃ constants\nc₁+c₂=>c₃ for c₁,c₂,c₃ constants\nc₁×(c₂×x) => (c₁×c₂)×x  for c₁,c₂ constants","category":"page"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"These rules are generally safe in the sense of obeying IEEE floating point arithmetic rules. However if the runtime value of x happens to be NaN or Inf the FD expression x*0 will identically return 0, because it will have been rewritten to 0 by the simplification rules. The expected IEEE result is NaN.","category":"page"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"[1]: More rules may be added in future versions of FD to improve efficiency.","category":"page"},{"location":"howitworks/","page":"How it works","title":"How it works","text":"[2]: See the D*  paper for an explanation of derivative graph factorization. ","category":"page"},{"location":"limitations/#Limitations","page":"Limitations","title":"Limitations","text":"","category":"section"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"FD does not support expressions with conditionals on FD variables. For example, you can do this:","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"julia> f(a,b,c) = a< 1.0 ? cos(b) : sin(c)\nf (generic function with 2 methods)\n\njulia> f(0.0,x,y)\ncos(x)\n\njulia> f(1.0,x,y)\nsin(y)","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"but you can't do this:","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"julia> f(a,b) = a < b ? cos(a) : sin(b)\nf (generic function with 2 methods)\n\njulia> f(x,y)\nERROR: MethodError: no method matching isless(::FastDifferentiation.Node{Symbol, 0}, ::FastDifferentiation.Node{Symbol, 0})\n\nClosest candidates are:\n  isless(::Any, ::DataValues.DataValue{Union{}})\n   @ DataValues ~/.julia/packages/DataValues/N7oeL/src/scalar/core.jl:291\n  isless(::S, ::DataValues.DataValue{T}) where {S, T}\n   @ DataValues ~/.julia/packages/DataValues/N7oeL/src/scalar/core.jl:285\n  isless(::DataValues.DataValue{Union{}}, ::Any)\n   @ DataValues ~/.julia/packages/DataValues/N7oeL/src/scalar/core.jl:293\n  ...","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"This is because the call f(x,y) creates an expression graph. At graph creation time the FD variables x,y are unevaluated variables with no specific value so they cannot be compared with any other value.","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"The algorithm can be extended to work with conditionals applied to FD variables but the processing time and graph size may grow exponentially with conditional nesting depth. A future version may allow for limited conditional nesting. See Future Work for a potential long term solution to this problem.","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"The preprocessing/compilation step for expressions graphs with more than ≈10⁵ operations may take a minute or more (processing time increase non-linearly with number of expressions so smaller expression have much shorter preprocessing times). This is due to two factors. ","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"The current code is not memory efficient - it allocates much more than necessary which makes it slower than it should be. Future versions will be more memory efficient.","category":"page"},{"location":"limitations/","page":"Limitations","title":"Limitations","text":"The code uses BitVector for tracking reachability of function roots and variable nodes. This seemed like a good idea when I began and thought FD would only be practical for modest size expressions (<10⁴ operations). But, it scaled better than expected and for larger graphs the memory overhead of the BitVector representation is significant. Using Set instead of BitVector for larger graphs should significantly reduce symbolic processing time.","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"CurrentModule = FastDifferentiation","category":"page"},{"location":"#Introduction","page":"Introduction","title":"Introduction","text":"","category":"section"},{"location":"","page":"Introduction","title":"Introduction","text":"(Image: Build Status)","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"FastDifferentiation (FD) is a package for generating efficient executables to evaluate derivatives of Julia functions. It can also generate efficient true symbolic derivatives for symbolic analysis. Unlike forward and reverse mode automatic differentiation FD automatically generates efficient derivatives for arbitrary function types: ℝ¹->ℝ¹, ℝ¹->ℝᵐ, ℝⁿ->ℝ¹, and ℝⁿ->ℝᵐ, m≠1,n≠1. ","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"For f:ℝⁿ->ℝᵐ with n,m large FD may have better performance than conventional AD algorithms because the FD algorithm finds expressions shared between partials and computes them only once. In some cases FD derivatives can be as efficient as manually coded derivatives[2].","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"FD may take much less time to compute symbolic derivatives than Symbolics.jl even in the ℝ¹->ℝ¹ case. The executables generated by FD may also be much faster (see Symbolic Processing[1]. ","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"You should consider using FastDifferentiation when you need: ","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"a fast executable for evaluating the derivative of a function and the overhead of the preprocessing/compilation time is swamped by evaluation time.\nto do additional symbolic processing on your derivative. FD can generate a true symbolic derivative to be processed further in Symbolics.jl or another computer algebra system.","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"This is the FD feature set:","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":" Dense Jacobian Sparse Jacobian Dense Hessian Sparse Hessian Higher order derivatives Jᵀv Hv\nCompiled function ✅ ✅ ✅ ✅ ✅ ✅ ✅\nSymbolic expression ✅ ✅ ✅ ✅ ✅ ✅ ✅","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"Jᵀv and Jv compute the Jacobian transpose times a vector and the Jacobian times a vector, without explicitly forming the Jacobian matrix. For applications see this paper. ","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"Hv computes the Hessian times a vector without explicitly forming the Hessian matrix. This can be useful when the Hessian matrix is large and sparse.","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"If you use FD in your work please share the functions you differentiate with me. I'll add them to the benchmarks. The more functions available to test the easier it is for others to determine if FD will help with their problem.","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"This is beta software being modified on a daily basis. Expect bugs and frequent, possibly breaking changes, over the next month or so. Documentation is frequently updated so check the latest docs before filing an issue. Your problem may have been fixed and documented.","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"[1]: I am working with the SciML team to see if it is possible to integrate FD differentiation directly into Symbolics.jl.","category":"page"},{"location":"","page":"Introduction","title":"Introduction","text":"[2]: See the Lagrangian dynamics example in the D*  paper.","category":"page"}]
}
