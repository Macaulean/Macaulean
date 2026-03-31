#!/usr/bin/env python3
"""
SymPy JSON-RPC server for Macaulean.
Long-lived process communicating via LSP base protocol (Content-Length headers)
over stdin/stdout. Same architecture as m2/macaulean.m2.
"""

import sys
import json
from sympy import symbols, Poly, groebner, ZZ, factorint, reduced
from sympy.polys.orderings import lex, grlex, grevlex

# ============================================================================
# Polynomial conversion: Macaulean JSON <-> SymPy
# ============================================================================

def make_ring(num_vars):
    """Create SymPy symbols x0, x1, ..., x_{n-1}."""
    if num_vars == 0:
        return []
    return list(symbols(' '.join(f'x{i}' for i in range(num_vars))))

def poly_data_to_sympy(data, syms):
    """Convert Macaulean PolynomialData to a SymPy expression.

    Format: [[coeff, [[var_idx, power], ...]], ...]
    """
    if not syms:
        # Constant polynomial
        return sum(term[0] for term in data)
    expr = 0
    for term in data:
        coeff = term[0]
        monomial = term[1]
        mon_expr = coeff
        for vp in monomial:
            var_idx, power = vp[0], vp[1]
            if var_idx < len(syms):
                mon_expr *= syms[var_idx] ** power
        expr += mon_expr
    return expr

def sympy_to_poly_data(poly_expr, syms):
    """Convert a SymPy polynomial expression to Macaulean PolynomialData format."""
    if not syms:
        # Constant
        val = int(poly_expr) if poly_expr else 0
        return [[val, []]]

    try:
        p = Poly(poly_expr, *syms, domain=ZZ)
    except Exception:
        # If it's just a constant
        val = int(poly_expr) if poly_expr else 0
        return [[val, []]]

    result = []
    for monom, coeff in p.as_dict().items():
        coeff_int = int(coeff)
        exponents = []
        for i, exp in enumerate(monom):
            if exp != 0:
                exponents.append([i, int(exp)])
        result.append([coeff_int, exponents])

    if not result:
        return [[0, []]]
    return result

def get_order(order_str):
    """Map order string to SymPy ordering."""
    orders = {'lex': lex, 'grlex': grlex, 'grevlex': grevlex}
    return orders.get(order_str, grevlex)

# ============================================================================
# RPC methods
# ============================================================================

def handle_quotient_remainder(params):
    """Polynomial reduction: element modulo ideal generators."""
    num_vars = params['numVars']
    poly_data = params['polyData']
    ideal_data = params['idealData']

    syms = make_ring(num_vars)
    f = poly_data_to_sympy(poly_data, syms)
    gens = [poly_data_to_sympy(g, syms) for g in ideal_data]

    if not gens or not syms:
        return {
            'ok': False,
            'status': 'empty generators or no variables',
            'quotients': [],
            'remainder': poly_data
        }

    # Use SymPy's reduced for multivariate polynomial division
    f_poly = Poly(f, *syms, domain=ZZ)
    gen_polys = [Poly(g, *syms, domain=ZZ) for g in gens]
    quot_polys, rem_poly = reduced(f_poly, gen_polys, *syms, domain=ZZ)

    quotients_data = [sympy_to_poly_data(q.as_expr(), syms) for q in quot_polys]
    remainder_data = sympy_to_poly_data(rem_poly.as_expr(), syms)

    return {
        'ok': True,
        'status': 'ok',
        'quotients': quotients_data,
        'remainder': remainder_data
    }

def handle_groebner_basis(params):
    """Compute Gröbner basis of an ideal."""
    num_vars = params['numVars']
    generators = params['generators']
    order = params.get('order', 'grevlex')

    syms = make_ring(num_vars)
    gens = [poly_data_to_sympy(g, syms) for g in generators]

    if not gens or not syms:
        return {'generators': generators}

    ordering = get_order(order)
    gb = groebner(gens, *syms, order=ordering, domain=ZZ)

    basis_data = [sympy_to_poly_data(p, syms) for p in gb.polys]
    return {'generators': basis_data}

def handle_factor_int(params):
    """Factor a natural number."""
    n = params[0] if isinstance(params, list) else params
    n = int(n)
    if n <= 1:
        return [[n, 1]]
    factors = factorint(n)
    return [[int(p), int(e)] for p, e in sorted(factors.items())]

# ============================================================================
# JSON-RPC / LSP base protocol
# ============================================================================

METHODS = {
    'quotientRemainderPolyData': handle_quotient_remainder,
    'groebnerBasis': handle_groebner_basis,
    'factorInt': handle_factor_int,
}

def read_lsp_message(stream):
    """Read an LSP base protocol message from stream."""
    headers = {}
    while True:
        line = stream.readline()
        if not line:
            return None  # EOF
        line = line.strip()
        if line == '':
            break
        if ':' in line:
            key, value = line.split(':', 1)
            headers[key.strip()] = value.strip()

    content_length = int(headers.get('Content-Length', 0))
    if content_length == 0:
        return None

    body = stream.read(content_length)
    return json.loads(body)

def write_lsp_message(stream, obj):
    """Write an LSP base protocol message to stream."""
    body = json.dumps(obj)
    header = f'Content-Length: {len(body)}\r\n\r\n'
    stream.write(header)
    stream.write(body)
    stream.flush()

def handle_request(request):
    """Process a JSON-RPC request and return a response."""
    req_id = request.get('id')
    method = request.get('method', '')
    params = request.get('params', {})

    handler = METHODS.get(method)
    if handler is None:
        return {
            'jsonrpc': '2.0',
            'id': req_id,
            'error': {'code': -32601, 'message': f'Method not found: {method}'}
        }

    try:
        result = handler(params)
        return {
            'jsonrpc': '2.0',
            'id': req_id,
            'result': result
        }
    except Exception as e:
        return {
            'jsonrpc': '2.0',
            'id': req_id,
            'error': {'code': -32000, 'message': str(e)}
        }

def main():
    print('Macaulean SymPy backend started', file=sys.stderr)

    # Use binary stdin for reliable reading, text stdout for writing
    stdin = sys.stdin
    stdout = sys.stdout

    while True:
        request = read_lsp_message(stdin)
        if request is None:
            break

        response = handle_request(request)
        write_lsp_message(stdout, response)

    print('Macaulean SymPy backend finished', file=sys.stderr)

if __name__ == '__main__':
    main()
