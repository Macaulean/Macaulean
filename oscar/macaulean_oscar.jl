#!/usr/bin/env julia
"""
Oscar JSON-RPC server for Macaulean.
Long-lived process communicating via LSP base protocol over stdin/stdout.
Same architecture as m2/macaulean.m2 and sympy/macaulean_sympy.py.
"""

# Suppress Oscar's banner from going to stdout
# Redirect stdout during loading, then restore
original_stdout = stdout
redirect_stdout(stderr) do
    @eval using Oscar
end
using JSON

# ============================================================================
# Polynomial conversion: Macaulean JSON <-> Oscar
# ============================================================================

function make_ring(num_vars::Int)
    if num_vars == 0
        return ZZ, Symbol[]
    end
    varnames = ["x$i" for i in 0:(num_vars-1)]
    R, vars = polynomial_ring(ZZ, varnames)
    return R, vars
end

function poly_data_to_oscar(data, R, vars)
    if isempty(vars)
        return R(sum(term[1] for term in data; init=0))
    end
    result = zero(R)
    for term in data
        coeff = term[1]
        monomial = term[2]
        mon = one(R) * coeff
        for vp in monomial
            var_idx = vp[1] + 1  # Julia is 1-indexed
            power = vp[2]
            if var_idx <= length(vars)
                mon *= vars[var_idx]^power
            end
        end
        result += mon
    end
    return result
end

function oscar_to_poly_data(f, vars)
    if isempty(vars)
        c = iszero(f) ? 0 : Int(constant_coefficient(f))
        return [[c, []]]
    end
    result = []
    for (coeff, exp_vec) in zip(coefficients(f), exponents(f))
        c = Int(coeff)
        exponents_list = []
        for (i, e) in enumerate(exp_vec)
            if e != 0
                push!(exponents_list, [i-1, Int(e)])  # back to 0-indexed
            end
        end
        push!(result, [c, exponents_list])
    end
    if isempty(result)
        return [[0, []]]
    end
    return result
end

# ============================================================================
# RPC methods
# ============================================================================

function handle_quotient_remainder(params)
    num_vars = params["numVars"]
    poly_data = params["polyData"]
    ideal_data = params["idealData"]

    R, vars = make_ring(num_vars)
    f = poly_data_to_oscar(poly_data, R, vars)
    gens = [poly_data_to_oscar(g, R, vars) for g in ideal_data]

    I = ideal(R, gens)
    # Use Oscar's reduce for ideal reduction
    # Oscar's normal_form or reduce
    quotients = []
    remainder = f
    for g in gens
        q, remainder = divrem(remainder, g)
        push!(quotients, q)
    end

    return Dict(
        "ok" => true,
        "status" => "ok",
        "quotients" => [oscar_to_poly_data(q, vars) for q in quotients],
        "remainder" => oscar_to_poly_data(remainder, vars)
    )
end

function handle_groebner_basis(params)
    num_vars = params["numVars"]
    generators = params["generators"]

    R, vars = make_ring(num_vars)
    gens = [poly_data_to_oscar(g, R, vars) for g in generators]

    I = ideal(R, gens)
    gb = groebner_basis(I)

    return Dict(
        "generators" => [oscar_to_poly_data(p, vars) for p in gb]
    )
end

function handle_poly_factorization(params)
    num_vars = params["numVars"]
    polynomial = params["polynomial"]

    R, vars = make_ring(num_vars)
    f = poly_data_to_oscar(polynomial, R, vars)

    fac = factor(f)
    result_factors = []

    # Include unit if not 1
    u = unit(fac)
    if !isone(u) && !isone(-u)
        push!(result_factors, oscar_to_poly_data(u, vars))
    elseif isone(-u)
        push!(result_factors, [[-1, []]])
    end

    for (factor_poly, mult) in fac
        factor_data = oscar_to_poly_data(factor_poly, vars)
        for _ in 1:mult
            push!(result_factors, factor_data)
        end
    end

    return Dict("factors" => result_factors)
end

function handle_factor_int(params)
    n = params isa AbstractVector ? params[1] : params
    n = Int(n)
    if n <= 1
        return [[n, 1]]
    end
    fac = factor(ZZ(n))
    return [[Int(p), Int(e)] for (p, e) in fac]
end

function handle_radical_membership(params)
    num_vars = params["numVars"]
    poly_data = params["polyData"]
    ideal_data = params["idealData"]

    R, vars = make_ring(num_vars)
    f = poly_data_to_oscar(poly_data, R, vars)
    gens = [poly_data_to_oscar(g, R, vars) for g in ideal_data]

    # Try successive powers
    for n in 1:99
        fn = f^n
        remainder = fn
        quotients = []
        for g in gens
            q, remainder = divrem(remainder, g)
            push!(quotients, q)
        end
        if iszero(remainder)
            return Dict(
                "inRadical" => true,
                "power" => n,
                "quotients" => [oscar_to_poly_data(q, vars) for q in quotients]
            )
        end
    end

    return Dict("inRadical" => false, "power" => 0, "quotients" => [])
end

# ============================================================================
# JSON-RPC / LSP base protocol
# ============================================================================

function handle_perm_group_membership(params)
    n = params["size"]  # permutation degree
    generators = params["generators"]  # array of permutation images
    target = params["target"]  # target permutation images

    G = symmetric_group(n)

    # Convert image arrays to Oscar permutations
    gen_perms = [perm(G, Vector{Int}(g)) for g in generators]
    target_perm = perm(G, Vector{Int}(target))

    # Build the subgroup
    H = sub(G, gen_perms)[1]

    # Check membership
    if !(target_perm in H)
        return Dict("inGroup" => false, "word" => Int[])
    end

    # Get word decomposition via GAP
    hom = GAP.Globals.EpimorphismFromFreeGroup(H.X)
    pre = GAP.Globals.PreImagesRepresentative(hom, target_perm.X)
    word = Vector{Int}(GAP.Globals.LetterRepAssocWord(pre))

    # Expand inverses: for each generator, compute its inverse as a product of generators
    # For now, include explicit inverse permutations as additional generators
    # and remap negative indices to positive ones.
    # Convention: generators 1..k are original, k+1..2k are their inverses
    n_gens = length(gen_perms)
    expanded_word = Int[]
    for letter in word
        if letter > 0
            push!(expanded_word, letter)
        else
            # Negative = inverse. Add n_gens to map to the inverse generator slot.
            push!(expanded_word, abs(letter) + n_gens)
        end
    end

    return Dict("inGroup" => true, "word" => expanded_word)
end

const METHODS = Dict(
    "quotientRemainderPolyData" => handle_quotient_remainder,
    "groebnerBasis" => handle_groebner_basis,
    "polyFactorization" => handle_poly_factorization,
    "radicalMembership" => handle_radical_membership,
    "factorInt" => handle_factor_int,
    "permGroupMembership" => handle_perm_group_membership,
)

function read_lsp_message(io)
    headers = Dict{String,String}()
    while true
        line = readline(io; keep=false)
        # Strip any trailing \r
        line = rstrip(line, ['\r'])
        if isempty(line)
            break
        end
        if occursin(":", line)
            key, value = split(line, ":", limit=2)
            headers[strip(key)] = strip(value)
        end
    end

    content_length = parse(Int, get(headers, "Content-Length", "0"))
    if content_length == 0
        return nothing
    end

    body = String(read(io, content_length))
    return JSON.parse(body)
end

function write_lsp_message(io, obj)
    body = JSON.json(obj)
    # Must use \r\n line endings for LSP base protocol
    # Write as raw bytes to avoid any encoding issues
    bytes = Vector{UInt8}(codeunits("Content-Length: $(length(body))\r\n\r\n$(body)"))
    write(io, bytes)
    flush(io)
end

function handle_request(request)
    req_id = get(request, "id", nothing)
    method = get(request, "method", "")
    params = get(request, "params", Dict())

    handler = get(METHODS, method, nothing)
    if handler === nothing
        return Dict(
            "jsonrpc" => "2.0",
            "id" => req_id,
            "error" => Dict("code" => -32601, "message" => "Method not found: $method")
        )
    end

    try
        result = handler(params)
        return Dict("jsonrpc" => "2.0", "id" => req_id, "result" => result)
    catch e
        return Dict(
            "jsonrpc" => "2.0",
            "id" => req_id,
            "error" => Dict("code" => -32000, "message" => sprint(showerror, e))
        )
    end
end

function main()
    println(stderr, "Macaulean Oscar backend started")

    while !eof(stdin)
        request = read_lsp_message(stdin)
        if request === nothing
            break
        end
        response = handle_request(request)
        write_lsp_message(stdout, response)
    end

    println(stderr, "Macaulean Oscar backend finished")
end

main()
