from functools import wraps
from timeit import default_timer

def ET(func):
    """
    Evaluating Execution Time
    """
    @wraps(func)
    def ExecutionTime(*args, **kwargs):
        sTime=default_timer()
        result = func(*args, **kwargs)
        eTime=default_timer()
        end=eTime - sTime
        minute,second=divmod(end,60)
        hour,minute=divmod(minute,60)
        print("%s took %fh %f m %fs" %(func.__name__,hour,minute,second))
        return result
    return ExecutionTime

#------------------------------------------------------------ cut line
from sympy import symbols,Symbol,Expr,Pow, Mul, Add,Rational,Basic,Integer,S
from sympy import postorder_traversal, preorder_traversal, flatten, expand,srepr
from sympy.logic.boolalg import sympify,Xor
def flatten_sympy(iterables):
    """
    flatten iterables with sympy item.
    """
    result=[]
    if(isinstance(iterables,Symbol) or isinstance(iterables,Expr) or isinstance(iterables,str)):
        return [iterables]
    
    for item in iterables:
        if(isinstance(item,tuple) or isinstance(item,list)or isinstance(item,set)):
            result.extend(flatten(item))
        else:
            result.append(item)
    return result

def sympy_simplify_and_remove_constants(expr: Expr) -> Expr:
    """
    Process constant item and coefficient.
    """
    replacements = {}

    for node in postorder_traversal(expr):
        if isinstance(node, Symbol):
            continue
        # Mul
        if isinstance(node, Mul):
            coeff, rest = node.as_coeff_Mul()
            if(coeff==1):
                continue
            if coeff.is_Number and not node.free_symbols:
                replacements[node] = S.Zero
                continue
            elif coeff.is_Number and node.free_symbols:
                if(coeff%2==0):
                    replacements[node] = S.Zero
                    continue
                else:
                    replacements[node] = rest
        # Add
        if isinstance(node, Add):
            coeff, rest = node.as_coeff_Add()
            if(coeff==0):
                continue
            if coeff.is_Number and not node.free_symbols:
                replacements[node] = S.Zero
                continue
            elif coeff.is_Number and node.free_symbols:
                replacements[node] = rest
    if(replacements):
        expr=expr.xreplace(replacements)

    return expr


def sympy_expand_pow_to_mul(expr: Expr) -> Expr:
    """
    ** -> Mul
    """
    replacements = {}  

    for node in postorder_traversal(expr):
        
        if(isinstance(node, Mul) or isinstance(node, Add)):
            if(not node.atoms()-node.free_symbols): 
                continue
            vars_args=node.args
            pow=False
            args_list=[]
            for arg in vars_args:
                if(isinstance(arg, Pow)):
                    pow=True
                    base, exp = arg.args
                    if exp.is_Integer and exp.is_positive:
                        expanded = Mul(*[base] * int(exp), evaluate=False)
                        args_list.append(expanded)
                else:
                    args_list.append(arg)
            if(pow):
                replacements[node]=node.func(*args_list, evaluate=False)

    if(replacements):
        expr=expr.xreplace(replacements)
    return expr


def simplify_expr_by_invert_random(expr: Expr, randoms: set, invert: set, compiled_patterns: dict) -> Expr:
    """
    invert Mul random = random
    """
    expr_str = str(expr)

    random_counts = {
        r: len(compiled_patterns[str(r)].findall(expr_str))
        for r in randoms
    }
    unique_randoms = {symbols(r) for r, count in random_counts.items() if count == 1}
    if not unique_randoms:
        return expr

    replacements = {}  
    for node in postorder_traversal(expr):
        if(isinstance(node, Mul)):
            vars_args = set(node.args)
            rand_syms = vars_args & unique_randoms
            other_syms = vars_args - rand_syms
            if len(rand_syms) == 1 and other_syms.issubset(invert):
                replacements[node]=next(iter(rand_syms))

    if(replacements):
        expr=expr.xreplace(replacements)
    return expr

def deep_once_restore(expr: Basic, subs: dict) -> Basic:
    """
    reverse Xreplace with subs dict (Xreplace sequence).
    """
    result = expr
    applied = set()  
    changed = True

    while changed:
        changed = False
        for var, replacement in subs.items():
            if var not in applied and var in result.free_symbols:
                new = result.xreplace({var: replacement})
                if new != result:
                    result = new
                    applied.add(var)
                    changed = True

    return result

import numpy as np
def compile_sympy_to_gf(exprs, vars_list, GF_field):
    """
    sympy expression -> efficiently computing MI on F_q
    """
    symbol_to_idx = {s: i for i, s in enumerate(vars_list)}
    is_binary_ext = GF_field.characteristic == 2 and GF_field.degree > 1
    def evaluate_expr_gfp(vals, expr):
        if expr.is_Rational:
            p_val, q_val = expr.as_numer_denom()
            scalar = GF_field(int(p_val) % GF_field.order) / GF_field(int(q_val) % GF_field.order)
            return GF_field([scalar] * vals.shape[0])

        elif expr.is_Number:
            scalar = GF_field(int(expr) % GF_field.order)
            return GF_field([scalar] * vals.shape[0])

        elif expr.is_Symbol:
            return vals[:, symbol_to_idx[expr]]

        elif expr.is_Add:
            args = [evaluate_expr_gfp(vals, arg) for arg in expr.args]
            result = args[0]
            for r in args[1:]:
                result = result + r
            return result

        elif expr.is_Mul:
            args = [evaluate_expr_gfp(vals, arg) for arg in expr.args]
            result = args[0]
            for r in args[1:]:
                result = result * r
            return result

        elif expr.is_Pow:
            base, exp = expr.args
            base_res = evaluate_expr_gfp(vals, base)
            if exp.is_Number and int(exp) == exp:
                exp_int = int(exp)
                if exp_int < 0 and (base_res == 0).any():
                    raise ZeroDivisionError("GFArray exists 0")
                return base_res ** exp_int
            else:
                raise TypeError("Non-integer exponent")

        else:
            raise TypeError(f"Unsupported sympy expression type: {type(expr)} - {expr}")

    def evaluate_expr_gf2n(vals, expr):
        if expr.is_Rational:
            p, q = expr.as_numer_denom()
            p_val, q_val = abs(int(p)), int(q)
            
            scalar_result = GF_field(p_val) * (GF_field(q_val)**(-1))
            return GF_field(np.full(vals.shape[0], int(scalar_result)))
            
        elif expr.is_Number:
            
            return GF_field(np.full(vals.shape[0], int(expr)))
            
        elif expr.is_Symbol:
            return vals[:, symbol_to_idx[expr]]
            
        elif expr.is_Add:
            args_results = [evaluate_expr_gf2n(vals, arg) for arg in expr.args]
            
            result = args_results[0]
            for i in range(1, len(args_results)):
                result = result + args_results[i]
            return result
            
        elif expr.is_Mul:
            args_results = [evaluate_expr_gf2n(vals, arg) for arg in expr.args]
            
            result = args_results[0]
            for i in range(1, len(args_results)):
                result = result * args_results[i]
            return result
            
        elif expr.is_Pow:
            base, exp = expr.args
            base_result = evaluate_expr_gf2n(vals, base)
            exp_int = int(exp)
            
            if exp_int == 0:
                return GF_field(np.ones(vals.shape[0], dtype=int))
            elif exp_int == 1:
                return base_result
            elif exp_int == -1:
                return base_result ** (-1)
            elif exp_int > 1:
                
                return base_result ** exp_int
            else: 
                return (base_result ** abs(exp_int)) ** (-1)
                
        else:
            raise TypeError(f"Unsupported sympy expression type: {type(expr)} - {expr}")
    
    if(is_binary_ext):
        return [lambda vals, e=expr: evaluate_expr_gf2n(vals, e) for expr in exprs]
    return [lambda vals, e=expr: evaluate_expr_gfp(vals, e) for expr in exprs]

from treelib import Tree
def createTreeFromExpr(expr):
    """
    ympy expression -> tree
    
    Example:
    >>> expr = Xor(And(a, b), Not(c))
    >>> tree = createTreeFromExpr(expr)
    >>> tree.show()
    Xor
    ├── And
    │   ├── a
    │   └── b
    └── Not
        └── c
    
    """
    expr=sympify(expr,convert_xor=False)
    whoreTree=Tree()
    rootList=[]
    for argID,arg in enumerate(preorder_traversal(expr)):
        
        if(argID==0): 
            whoreTree.create_node(tag=str(arg.func).replace(" ",""), identifier=str(argID), data=arg) 
            rootList.append([str(argID),len(arg.args)]) 
            continue
        if(str(arg.func)=="Xor" or str(arg.func)=="And"):
            parent=rootList.pop()
            parent[1]-=1
            whoreTree.create_node(tag=str(arg.func).replace(" ",""), identifier=str(argID), data=arg,parent=parent[0]) 
            if(parent[1]>0): 
                rootList.append(parent)
            rootList.append([str(argID),len(arg.args)])
        elif(str(arg.func)=="Not"): 
            parent=rootList.pop()
            parent[1]-=1
            whoreTree.create_node(tag=str(arg).replace(" ",""), identifier=str(argID), data=arg,parent=parent[0]) 
            if(parent[1]>0):
                rootList.append(parent)
            rootList.append(["Not",len(arg.args)])
        else: 
            parent=rootList.pop()
            if(parent[0]=="Not"): 
                continue
            parent[1]-=1
            whoreTree.create_node(tag=str(arg).replace(" ",""), identifier=str(argID), data=arg,parent=parent[0])
            if(parent[1]>0): 
                rootList.append(parent)
    return whoreTree

from sympy import Add as SympyAdd, Mul as SympyMul, Pow as SympyPow
from galois import GF
class sympyGF2N():
    """
    Supports SymPy in F_(2^n)
    """
    GF2n = None
    
    @classmethod
    def set_field(cls, field=GF(2**3)):
        """set GF(2^n) field"""
        cls.GF2n = field
    
    @classmethod
    def evaluate(cls, *exprs):
        if cls.GF2n is None:
            raise ValueError("set GF(2^n) field first: SympyGF2N.set_field(field)")
        
        if not exprs:
            return []
        
        if len(exprs) == 1 and isinstance(exprs[0], (list, tuple)):
            expr_list = exprs[0]
        else:
            expr_list = list(exprs)
        
        evaluated_exprs = []
        for expr in expr_list:
            expr = cls._evaluate_gf2n(expr)
            evaluated_exprs.append(expr)
        
        result = evaluated_exprs[0] if len(evaluated_exprs) == 1 else evaluated_exprs
        return result
    @classmethod
    def _evaluate_gf2n(cls, expr):
        if expr.is_Number:
            num = int(expr)
            if num < 0:
                num = abs(num)
            return Integer(int(cls.GF2n(num)))
        
        elif isinstance(expr, SympyAdd):
            flattened_terms = cls._flatten_add(expr)
            
            terms = []
            for term in flattened_terms:
                processed_term = cls._evaluate_gf2n(term)
                if processed_term != 0: 
                    terms.append(processed_term)
            
            from collections import defaultdict
            term_coeffs = defaultdict(int)
            
            for term in terms:
                if term.is_Number:
                    coeff = int(term)
                    term_coeffs[()] = cls._gf2n_add(term_coeffs[()], coeff) 
                elif isinstance(term, SympyMul):
                    coeff = 1
                    var_factors = []
                    for factor in term.args:
                        if factor.is_Number:
                            num_val = int(factor)
                            if num_val < 0:
                                num_val = abs(num_val)
                            coeff = cls._gf2n_multiply(coeff, num_val)
                        else:
                            var_factors.append(factor)
                    
                    if var_factors:
                        sorted_vars = sorted(var_factors, key=lambda x: str(x))
                        var_key = tuple(sorted_vars)  
                        term_coeffs[var_key] = cls._gf2n_add(term_coeffs[var_key], coeff)
                    else:
                        term_coeffs[()] = cls._gf2n_add(term_coeffs[()], coeff)
                else:
                    term_coeffs[(term,)] = cls._gf2n_add(term_coeffs[(term,)], 1)
            
            result_terms = []
            for var_key, coeff in term_coeffs.items():
                if coeff != 0:
                    if var_key == ():
                        result_terms.append(Integer(coeff))
                    else:
                        if len(var_key) == 1:
                            var_part = var_key[0]
                        else:
                            var_part = SympyMul(*var_key, evaluate=False)
                        
                        if coeff == 1:
                            result_terms.append(var_part)
                        else:
                            result_terms.append(SympyMul(Integer(coeff), var_part, evaluate=False))
            
            if not result_terms:
                return Integer(0)
            elif len(result_terms) == 1:
                return result_terms[0]
            else:
                return SympyAdd(*result_terms, evaluate=False)
        elif isinstance(expr, SympyMul):
            numeric_factors = 1
            other_factors = []
            
            for factor in expr.args:
                if isinstance(factor, Rational):

                    numerator = factor.p
                    denominator = factor.q
                    if numerator < 0:
                        numerator = abs(numerator)
                    if denominator < 0:
                        denominator = abs(denominator)
                    inv_denom = cls._gf2n_inverse(denominator)
                    numeric_factors = cls._gf2n_multiply(numeric_factors, cls._gf2n_multiply(numerator, inv_denom))
                elif isinstance(factor, SympyPow) and factor.exp == -1:
                    
                    base = cls._evaluate_gf2n(factor.base)
                    if base.is_Number:
                        num_val = int(base)
                        if num_val < 0:
                            num_val = abs(num_val)
                        numeric_factors = cls._gf2n_multiply(numeric_factors, cls._gf2n_inverse(num_val))
                    else:
                        other_factors.append(SympyPow(base, -1, evaluate=False))
                else:
                    processed_factor = cls._evaluate_gf2n(factor)
                    if processed_factor.is_Number:
                        num_val = int(processed_factor)
                        if num_val < 0:
                            num_val = abs(num_val)
                        numeric_factors = cls._gf2n_multiply(numeric_factors, num_val)
                    else:
                        other_factors.append(processed_factor)
            
            
            if numeric_factors == 1:
                if not other_factors:
                    return Integer(1)
                elif len(other_factors) == 1:
                    return other_factors[0]
                else:
                    return SympyMul(*other_factors, evaluate=False)
            else:
                if not other_factors:
                    return Integer(numeric_factors)
                else:
                    return SympyMul(Integer(numeric_factors), *other_factors, evaluate=False)
        
        elif isinstance(expr, SympyPow):
            
            base = cls._evaluate_gf2n(expr.base)
            exp = cls._evaluate_gf2n(expr.exp)
            
            if exp == -1:
                if base.is_Number:
                    num_val = int(base)
                    if num_val < 0:
                        num_val = abs(num_val)
                    return Integer(cls._gf2n_inverse(num_val))
                else:
                    return SympyPow(base, exp, evaluate=False)
            else:
                return SympyPow(base, exp, evaluate=False)
        
        elif isinstance(expr, Rational):
            
            numerator = expr.p
            denominator = expr.q
            if numerator < 0:
                numerator = abs(numerator)
            if denominator < 0:
                denominator = abs(denominator)
            inv_denom = cls._gf2n_inverse(denominator)
            result = cls._gf2n_multiply(numerator, inv_denom)
            return Integer(result)
        
        else:
            return expr

    @classmethod
    def add(cls, *terms):

        if cls.GF2n is None:
            raise ValueError("set GF(2^n) field first: SympyGF2N.set_field(field)")
        
        
        all_terms = []
        for term in terms:
            if isinstance(term, SympyAdd):
                all_terms.extend(term.args)
            else:
                all_terms.append(term)
        
        expr = SympyAdd(*all_terms, evaluate=False)
        return cls.evaluate(expr)
    
    @classmethod
    def mul(cls, *factors):
        
        if cls.GF2n is None:
            raise ValueError("set GF(2^n) field first: SympyGF2N.set_field(field)")
        
        expr = SympyMul(*factors, evaluate=False)
        return cls.evaluate(expr)
    @classmethod
    def expand(cls, expr):
        if cls.GF2n is None:
            raise ValueError("set GF(2^n) field first: SympyGF2N.set_field(field)")
        
        old = None
        
        while True:
           
            expr = cls.evaluate(expr)
            
            
            h = hash(expr.srepr() if hasattr(expr, 'srepr') else str(expr))
            if h == old:
                return expr
            old = h
            
            
            expr = cls._distribute_once(expr)

    @classmethod
    def _distribute_once(cls, expr):

       
        if isinstance(expr, SympyAdd):
            return SympyAdd(*[cls._distribute_once(a) for a in expr.args], evaluate=False)
        
        
        if isinstance(expr, SympyMul):
            args = list(expr.args)
            
            
            for i, a in enumerate(args):
                if isinstance(a, SympyAdd):
                   
                    rest = args[:i] + args[i+1:]
                    
                   
                    expanded_terms = []
                    for term in a.args:
                        
                        new_product = SympyMul(term, *rest, evaluate=False)
                        
                        expanded_terms.append(
                            cls._flatten_mul(
                                cls._distribute_once(new_product)
                            )
                        )
                    
                    if not expanded_terms:
                        return Integer(0)
                    elif len(expanded_terms) == 1:
                        return expanded_terms[0]
                    else:
                        return SympyAdd(*expanded_terms, evaluate=False)
            
            
            return cls._flatten_mul(
                SympyMul(*[cls._distribute_once(a) for a in args], evaluate=False)
            )
        
        
        if isinstance(expr, SympyPow):
            return SympyPow(cls._distribute_once(expr.base), expr.exp, evaluate=False)
        
        return expr
    
    @classmethod
    def _flatten_mul(cls, expr):
        if not isinstance(expr, SympyMul):
            return expr
        
        flat = []
        for a in expr.args:
            if isinstance(a, SympyMul):
                flat.extend(a.args)
            else:
                flat.append(a)
        
        if not flat:
            return Integer(1)
        elif len(flat) == 1:
            return flat[0]
        else:
            return SympyMul(*flat, evaluate=False)
    
    @classmethod
    def xreplace(cls, expr, rule):
        def _replace(e):
            if e in rule:
                return rule[e]
            elif e.is_Atom:
                return e
            elif isinstance(e, SympyAdd):
                new_args = [_replace(arg) for arg in e.args]
                return SympyAdd(*new_args, evaluate=False)
            elif isinstance(e, SympyMul):
                new_args = [_replace(arg) for arg in e.args]
                return SympyMul(*new_args, evaluate=False)
            elif isinstance(e, SympyPow):
                base = _replace(e.base)
                exp = _replace(e.exp)
                return SympyPow(base, exp, evaluate=False)
            else:
                return e
        
        replaced_expr = _replace(expr)
        return cls.evaluate(replaced_expr)
    
    @classmethod
    def random_coeff_invertibleTransform_v1(cls, expr, random):

        if cls.GF2n is None:
            raise ValueError("set GF(2^n) field first: SympyGF2N.set_field(field)")
        
       
        random_coeff = expr.coeff(random)
        
        if not random_coeff.is_Number:
            return expr  
        if random_coeff == 0:
            return expr  
        
        if random_coeff == 1:
            return expr  
        
        
        try:
            inv_coeff = int(cls.GF2n(int(random_coeff))**-1)
        except (ValueError, ZeroDivisionError):
            return expr 
        
        
        if isinstance(expr, SympyAdd):
            new_terms = []
            for term in expr.args:
                if term.has(random):
                    
                    coeff = term.coeff(random)
                    other_part = term / coeff if coeff != 0 else term
                   
                    new_coeff = int(cls.GF2n(int(coeff)) * cls.GF2n(inv_coeff))
                    
                    if new_coeff == 1 and other_part == random:
                        new_terms.append(random)
                    else:
                        new_terms.append(SympyMul(Integer(new_coeff), other_part, evaluate=False))
                else:
                   
                    if term.is_Number:
                        new_coeff = int(cls.GF2n(int(term)) * cls.GF2n(inv_coeff))
                        new_terms.append(Integer(new_coeff))
                    else:
                        
                        coeff_part = term.as_coeff_Mul()[0]
                        other_part = term.as_coeff_Mul()[1]
                        new_coeff = int(cls.GF2n(int(coeff_part)) * cls.GF2n(inv_coeff))
                        if new_coeff == 1:
                            new_terms.append(other_part)
                        else:
                            new_terms.append(SympyMul(Integer(new_coeff), other_part, evaluate=False))
            return SympyAdd(*new_terms, evaluate=False)
        else:
            
            if expr.has(random):
                coeff = expr.coeff(random)
                other_part = expr / coeff if coeff != 0 else expr
                new_coeff = int(cls.GF2n(int(coeff)) * cls.GF2n(inv_coeff))
                
                if new_coeff == 1 and other_part == random:
                    return random
                else:
                    return SympyMul(Integer(new_coeff), other_part, evaluate=False)
            else:
                if expr.is_Number:
                    return Integer(int(cls.GF2n(int(expr)) * cls.GF2n(inv_coeff)))
                else:
                    coeff_part = expr.as_coeff_Mul()[0]
                    other_part = expr.as_coeff_Mul()[1]
                    new_coeff = int(cls.GF2n(int(coeff_part)) * cls.GF2n(inv_coeff))
                    if new_coeff == 1:
                        return other_part
                    else:
                        return SympyMul(Integer(new_coeff), other_part, evaluate=False)
    @classmethod
    def random_coeff_invertibleTransform_v2(cls, expr, random):

        if cls.GF2n is None:
            raise ValueError("set GF(2^n) field first: SympyGF2N.set_field(field)")
        
        
        random_coeff = expr.coeff(random)
        
        if not random_coeff.is_Number:
            return expr  
        if random_coeff == 0:
            return expr  
        
        if random_coeff == 1:
            return expr 
        
        
        try:
            inv_coeff = int(cls.GF2n(int(random_coeff))**-1)
        except (ValueError, ZeroDivisionError):
            return expr  
        
        
        def _gf_multiply(e, coeff):
            
            if e.is_Number:
                return Integer(int(cls.GF2n(int(e)) * cls.GF2n(coeff)))
            elif isinstance(e, SympyMul):
                
                numeric_factors = 1
                other_factors = []
                for factor in e.args:
                    if factor.is_Number:
                        numeric_factors = int(cls.GF2n(int(numeric_factors)) * cls.GF2n(int(factor)))
                    else:
                        other_factors.append(factor)
                
                new_numeric = int(cls.GF2n(int(numeric_factors)) * cls.GF2n(coeff))
                if new_numeric == 1:
                    return SympyMul(*other_factors, evaluate=False) if other_factors else Integer(1)
                else:
                    return SympyMul(Integer(new_numeric), *other_factors, evaluate=False)
            elif isinstance(e, SympyAdd):
                new_args = [_gf_multiply(arg, coeff) for arg in e.args]
                return SympyAdd(*new_args, evaluate=False)
            else:
                
                return SympyMul(Integer(int(cls.GF2n(coeff))), e, evaluate=False)
        
        
        return _gf_multiply(expr, inv_coeff)
    
    @classmethod
    def _gf2n_multiply(cls, a, b):
        
        return int(cls.GF2n(int(a)) * cls.GF2n(int(b)))
    
    @classmethod
    def _gf2n_add(cls, a, b):
        
        return int(cls.GF2n(int(a)) + cls.GF2n(int(b)))
    
    @classmethod
    def _gf2n_inverse(cls, a):
        
        if a == 0:
            raise ValueError("0 has no inverse in GF(2^n)")
        return int(cls.GF2n(int(a))**-1)
    @classmethod
    def _flatten_add(cls, expr):
        
        if isinstance(expr, SympyAdd):
            terms = []
            for arg in expr.args:
                
                terms.extend(cls._flatten_add(arg))
            return terms
        else:
           
            return [expr]



from sympy import Add as SympyAdd, Mul as SympyMul, Pow as SympyPow
from galois import GF
class sympyGFp():
    """
    Supports SymPy in F_(p)
    """
    GFp = None
    
    @classmethod
    def set_field(cls, field=GF(2**3-1)):
        """set GF(p) field first"""
        cls.GFp = field
    
    @classmethod
    def evaluate(cls, *exprs):
        if cls.GFp is None:
            raise ValueError("set GF(p) field first: SympyPrimeField.set_field(field)")
        
        
        if not exprs:
            return []
        
        if len(exprs) == 1 and isinstance(exprs[0], (list, tuple)):
            expr_list = exprs[0]
        else:
            expr_list = list(exprs)
        
        evaluated_exprs = []
        for expr in expr_list:
            
            expr = cls._evaluate_gfp(expr)
            evaluated_exprs.append(expr)
        
        result = evaluated_exprs[0] if len(evaluated_exprs) == 1 else evaluated_exprs
        return result
    
    @classmethod
    def _evaluate_gfp(cls, expr):
        if expr.is_Number:
           
            num = int(expr)
            if num < 0:
                
                num = cls.GFp.order - (abs(num) % cls.GFp.order)
            else:
                num = num % cls.GFp.order
            return Integer(int(cls.GFp(num)))
        
        elif isinstance(expr, SympyAdd):
            
            flattened_terms = cls._flatten_add(expr)
            
            
            terms = []
            for term in flattened_terms:
                processed_term = cls._evaluate_gfp(term)
                if processed_term != 0:  
                    terms.append(processed_term)
            
            
            from collections import defaultdict
            term_coeffs = defaultdict(int)
            
            for term in terms:
                if term.is_Number:
                    coeff = int(term)
                    term_coeffs[()] = (term_coeffs[()] + coeff) % cls.GFp.order  
                elif isinstance(term, SympyMul):
                    
                    coeff = 1
                    var_factors = []
                    for factor in term.args:
                        if factor.is_Number:
                            num_val = int(factor)
                            if num_val < 0:
                                num_val = cls.GFp.order - (abs(num_val) % cls.GFp.order)
                            else:
                                num_val = num_val % cls.GFp.order
                            coeff = (coeff * num_val) % cls.GFp.order
                        else:
                            var_factors.append(factor)
                    
                    if var_factors:
                        
                        sorted_vars = sorted(var_factors, key=lambda x: str(x))
                        var_key = tuple(sorted_vars)  
                        term_coeffs[var_key] = (term_coeffs[var_key] + coeff) % cls.GFp.order
                    else:
                        term_coeffs[()] = (term_coeffs[()] + coeff) % cls.GFp.order
                else:
                    
                    term_coeffs[(term,)] = (term_coeffs[(term,)] + 1) % cls.GFp.order
            
            
            result_terms = []
            for var_key, coeff in term_coeffs.items():
                if coeff != 0:
                    if var_key == ():  
                        result_terms.append(Integer(coeff))
                    else:
                        if len(var_key) == 1:
                            var_part = var_key[0]
                        else:
                            var_part = SympyMul(*var_key, evaluate=False)
                        
                        if coeff == 1:
                            result_terms.append(var_part)
                        else:
                            result_terms.append(SympyMul(Integer(coeff), var_part, evaluate=False))
            
            if not result_terms:
                return Integer(0)
            elif len(result_terms) == 1:
                return result_terms[0]
            else:
                return SympyAdd(*result_terms, evaluate=False)

        elif isinstance(expr, SympyMul):
           
            numeric_factors = 1
            other_factors = []
            
            for factor in expr.args:
                
                if isinstance(factor, Rational):
                    
                    numerator = factor.p
                    denominator = factor.q
                    
                    if numerator < 0:
                        numerator = cls.GFp.order - (abs(numerator) % cls.GFp.order)
                    else:
                        numerator = numerator % cls.GFp.order
                    if denominator < 0:
                        denominator = cls.GFp.order - (abs(denominator) % cls.GFp.order)
                    else:
                        denominator = denominator % cls.GFp.order
                    inv_denom = cls._prime_field_inverse(denominator)
                    factor_result = (numerator * inv_denom) % cls.GFp.order
                    numeric_factors = (numeric_factors * factor_result) % cls.GFp.order
                elif isinstance(factor, SympyPow) and factor.exp == -1:
                    
                    base = cls._evaluate_gfp(factor.base)
                    if base.is_Number:
                        num_val = int(base)
                        if num_val < 0:
                            num_val = cls.GFp.order - (abs(num_val) % cls.GFp.order)
                        else:
                            num_val = num_val % cls.GFp.order
                        inv_val = cls._prime_field_inverse(num_val)
                        numeric_factors = (numeric_factors * inv_val) % cls.GFp.order
                    else:
                        
                        processed_pow = cls._evaluate_gfp(SympyPow(base, -1, evaluate=False))
                        if processed_pow.is_Number:
                            numeric_factors = (numeric_factors * int(processed_pow)) % cls.GFp.order
                        else:
                            other_factors.append(processed_pow)
                else:
                    processed_factor = cls._evaluate_gfp(factor)
                    if processed_factor.is_Number:
                        num_val = int(processed_factor)
                        if num_val < 0:
                            num_val = cls.GFp.order - (abs(num_val) % cls.GFp.order)
                        else:
                            num_val = num_val % cls.GFp.order
                        numeric_factors = (numeric_factors * num_val) % cls.GFp.order
                    elif isinstance(processed_factor, SympyMul):
                        
                        sub_numeric = 1
                        sub_other = []
                        for sub_factor in processed_factor.args:
                            if sub_factor.is_Number:
                                sub_num_val = int(sub_factor)
                                if sub_num_val < 0:
                                    sub_num_val = cls.GFp.order - (abs(sub_num_val) % cls.GFp.order)
                                else:
                                    sub_num_val = sub_num_val % cls.GFp.order
                                sub_numeric = (sub_numeric * sub_num_val) % cls.GFp.order
                            else:
                                sub_other.append(sub_factor)
                        numeric_factors = (numeric_factors * sub_numeric) % cls.GFp.order
                        other_factors.extend(sub_other)
                    else:
                        other_factors.append(processed_factor)
            
            
            if numeric_factors == 0:
               
                return Integer(0)
            elif numeric_factors == 1:
                if not other_factors:
                    return Integer(1)
                elif len(other_factors) == 1:
                    return other_factors[0]
                else:
                    return SympyMul(*other_factors, evaluate=False)
            else:
                if not other_factors:
                    return Integer(numeric_factors)
                else:
                    return SympyMul(Integer(numeric_factors), *other_factors, evaluate=False)
        elif isinstance(expr, SympyPow):
            
            base = cls._evaluate_gfp(expr.base)
            exp = cls._evaluate_gfp(expr.exp)
            
            if exp == -1:
                if base.is_Number:
                    num_val = int(base)
                    if num_val < 0:
                        num_val = cls.GFp.order - (abs(num_val) % cls.GFp.order)
                    else:
                        num_val = num_val % cls.GFp.order
                    return Integer(cls._prime_field_inverse(num_val))
                else:
                    
                    return SympyPow(base, exp, evaluate=False)
            else:
                return SympyPow(base, exp, evaluate=False)
        
        elif isinstance(expr, Rational):
            
            numerator = expr.p
            denominator = expr.q
            
            if numerator < 0:
                numerator = cls.GFp.order - (abs(numerator) % cls.GFp.order)
            else:
                numerator = numerator % cls.GFp.order
            if denominator < 0:
                denominator = cls.GFp.order - (abs(denominator) % cls.GFp.order)
            else:
                denominator = denominator % cls.GFp.order
            inv_denom = cls._prime_field_inverse(denominator)
            result = (numerator * inv_denom) % cls.GFp.order
            return Integer(result)
        
        else:
            return expr
    
    @classmethod
    def add(cls, *terms):
        
        if cls.GFp is None:
            raise ValueError("set GF(p) field first: SympyPrimeField.set_field(field)")
        
        all_terms = []
        for term in terms:
            if isinstance(term, SympyAdd):
                all_terms.extend(term.args)
            else:
                all_terms.append(term)
        
        expr = SympyAdd(*all_terms, evaluate=False)
        return cls.evaluate(expr)
    
    @classmethod
    def mul(cls, *factors):
        
        if cls.GFp is None:
            raise ValueError("set GF(p) field first: SympyPrimeField.set_field(field)")
        
        expr = SympyMul(*factors, evaluate=False)
        return cls.evaluate(expr)
    
    @classmethod
    def expand(cls, expr):

        if cls.GFp is None:
            raise ValueError("set GF(p) field first: SympyPrimeField.set_field(field)")
        
        old = None
        
        while True:
           
            expr = cls.evaluate(expr)
            
           
            h = hash(expr.srepr() if hasattr(expr, 'srepr') else str(expr))
            if h == old:
                return expr
            old = h
            
            expr = cls._distribute_once(expr)
    
    @classmethod
    def _distribute_once(cls, expr):

        
        if isinstance(expr, SympyAdd):
            return SympyAdd(*[cls._distribute_once(a) for a in expr.args], evaluate=False)
        
        
        if isinstance(expr, SympyMul):
            args = list(expr.args)
            
            
            for i, a in enumerate(args):
                if isinstance(a, SympyAdd):
                   
                    rest = args[:i] + args[i+1:]
                    
                    
                    expanded_terms = []
                    for term in a.args:
                        
                        new_product = SympyMul(term, *rest, evaluate=False)
                        
                        expanded_terms.append(
                            cls._flatten_mul(
                                cls._distribute_once(new_product)
                            )
                        )
                    
                    
                    if not expanded_terms:
                        return Integer(0)
                    elif len(expanded_terms) == 1:
                        return expanded_terms[0]
                    else:
                        return SympyAdd(*expanded_terms, evaluate=False)
            
            
            return cls._flatten_mul(
                SympyMul(*[cls._distribute_once(a) for a in args], evaluate=False)
            )
        
        
        if isinstance(expr, SympyPow):
            
            return SympyPow(cls._distribute_once(expr.base), expr.exp, evaluate=False)
        
        
        return expr
    
    @classmethod
    def _flatten_mul(cls, expr):
        if not isinstance(expr, SympyMul):
            return expr
        
        flat = []
        for a in expr.args:
            if isinstance(a, SympyMul):
                flat.extend(a.args)
            else:
                flat.append(a)
        
        if not flat:
            return Integer(1)
        elif len(flat) == 1:
            return flat[0]
        else:
            return SympyMul(*flat, evaluate=False)
    @classmethod
    def xreplace(cls, expr, rule):
        
        rule = {key: -value for key, value in rule.items()}
        def _replace(e):
            if e in rule:
                return rule[e]
            elif e.is_Atom:
                return e
            elif isinstance(e, SympyAdd):
                new_args = [_replace(arg) for arg in e.args]
                return SympyAdd(*new_args, evaluate=False)
            elif isinstance(e, SympyMul):
                new_args = [_replace(arg) for arg in e.args]
                return SympyMul(*new_args, evaluate=False)
            elif isinstance(e, SympyPow):
                base = _replace(e.base)
                exp = _replace(e.exp)
                return SympyPow(base, exp, evaluate=False)
            else:
                return e
        
        replaced_expr = _replace(expr)
        return cls.evaluate(replaced_expr)
    
    @classmethod
    def random_coeff_invertibleTransform_v1(cls, expr, random):
        
        if cls.GFp is None:
            raise ValueError("set GF(p) field first: SympyPrimeField.set_field(field)")
        
        random_coeff = expr.coeff(random)
        
        if not random_coeff.is_Number:
            return expr  
        if random_coeff == 0:
            return expr
        
        if random_coeff == 1:
            return expr
        
        try:
            inv_coeff = int(cls.GFp(int(random_coeff))**-1)
        except (ValueError, ZeroDivisionError):
            return expr
        
        
        if isinstance(expr, SympyAdd):
            new_terms = []
            for term in expr.args:
                if term.has(random):
                    coeff = term.coeff(random)
                    other_part = term / coeff if coeff != 0 else term
                    new_coeff = int(cls.GFp(int(coeff)) * cls.GFp(inv_coeff))
                    if new_coeff == 1 and other_part == random:
                        new_terms.append(random)
                    else:
                        new_terms.append(SympyMul(Integer(new_coeff), other_part, evaluate=False))
                else:
                    if term.is_Number:
                        new_coeff = int(cls.GFp(int(term)) * cls.GFp(inv_coeff))
                        new_terms.append(Integer(new_coeff))
                    else:
                        coeff_part = term.as_coeff_Mul()[0]
                        other_part = term.as_coeff_Mul()[1]
                        new_coeff = int(cls.GFp(int(coeff_part)) * cls.GFp(inv_coeff))
                        if new_coeff == 1:
                            new_terms.append(other_part)
                        else:
                            new_terms.append(SympyMul(Integer(new_coeff), other_part, evaluate=False))
            return SympyAdd(*new_terms, evaluate=False)
        else:
            if expr.has(random):
                coeff = expr.coeff(random)
                other_part = expr / coeff if coeff != 0 else expr
                new_coeff = int(cls.GFp(int(coeff)) * cls.GFp(inv_coeff))
                if new_coeff == 1 and other_part == random:
                    return random
                else:
                    return SympyMul(Integer(new_coeff), other_part, evaluate=False)
            else:
                if expr.is_Number:
                    return Integer(int(cls.GFp(int(expr)) * cls.GFp(inv_coeff)))
                else:
                    coeff_part = expr.as_coeff_Mul()[0]
                    other_part = expr.as_coeff_Mul()[1]
                    new_coeff = int(cls.GFp(int(coeff_part)) * cls.GFp(inv_coeff))
                    if new_coeff == 1:
                        return other_part
                    else:
                        return SympyMul(Integer(new_coeff), other_part, evaluate=False)
    @classmethod
    def random_coeff_invertibleTransform_v2(cls, expr, random):

        if cls.GFp is None:
            raise ValueError("set GF(p) field first: SympyPrimeField.set_field(field)")
        
        
        random_coeff = expr.coeff(random)
        
        if not random_coeff.is_Number:
            return expr  
        if random_coeff == 0:
            return expr 
        
        if random_coeff == 1:
            return expr  
        
        try:
            inv_coeff = int(cls.GFp(int(random_coeff))**-1)
        except (ValueError, ZeroDivisionError):
            return expr  
        
        def _prime_field_multiply_expr(e, coeff):
            
            if e.is_Number:
                
                num_val = int(e)
                if num_val < 0:
                    num_val = cls.GFp.order - (abs(num_val) % cls.GFp.order)
                else:
                    num_val = num_val % cls.GFp.order
                result = int(cls.GFp(num_val) * cls.GFp(coeff))
                return Integer(result)
            
            elif isinstance(e, SympyMul):
                
                numeric_factors = 1
                other_factors = []
                
                for factor in e.args:
                    if factor.is_Number:
                        
                        num_val = int(factor)
                        if num_val < 0:
                            num_val = cls.GFp.order - (abs(num_val) % cls.GFp.order)
                        else:
                            num_val = num_val % cls.GFp.order
                        numeric_factors = int(cls.GFp(numeric_factors) * cls.GFp(num_val))
                    else:
                        other_factors.append(factor)
                
               
                new_numeric = int(cls.GFp(numeric_factors) * cls.GFp(coeff))
                
                
                if new_numeric == 0:
                    return Integer(0)
                elif new_numeric == 1:
                    if not other_factors:
                        return Integer(1)
                    elif len(other_factors) == 1:
                        return other_factors[0]
                    else:
                        return SympyMul(*other_factors, evaluate=False)
                else:
                    if not other_factors:
                        return Integer(new_numeric)
                    else:
                        return SympyMul(Integer(new_numeric), *other_factors, evaluate=False)
            
            elif isinstance(e, SympyAdd):
                
                new_args = [_prime_field_multiply_expr(arg, coeff) for arg in e.args]
                
                new_args = [arg for arg in new_args if arg != 0]
                
                if not new_args:
                    return Integer(0)
                elif len(new_args) == 1:
                    return new_args[0]
                else:
                    return SympyAdd(*new_args, evaluate=False)
            
            elif isinstance(e, SympyPow):
                
                base = _prime_field_multiply_expr(e.base, coeff)
                exp = e.exp  
                
                if base == 0:
                    return Integer(0)
                else:
                    return SympyPow(base, exp, evaluate=False)
            
            elif isinstance(e, Rational):
                
                numerator = e.p
                denominator = e.q
                
                
                if numerator < 0:
                    numerator = cls.GFp.order - (abs(numerator) % cls.GFp.order)
                else:
                    numerator = numerator % cls.GFp.order
                if denominator < 0:
                    denominator = cls.GFp.order - (abs(denominator) % cls.GFp.order)
                else:
                    denominator = denominator % cls.GFp.order
                
                
                inv_denom = cls._prime_field_inverse(denominator)
                result_val = int(cls.GFp(numerator) * cls.GFp(inv_denom) * cls.GFp(coeff))
                return Integer(result_val)
            
            else:
                
                return SympyMul(Integer(int(cls.GFp(coeff))), e, evaluate=False)
        
        
        return _prime_field_multiply_expr(expr, inv_coeff)
    @classmethod
    def _prime_field_multiply(cls, a, b):

        return int(cls.GFp(int(a)) * cls.GFp(int(b)))
    
    @classmethod
    def _prime_field_add(cls, a, b):
       
        return int(cls.GFp(int(a)) + cls.GFp(int(b)))
    
    @classmethod
    def _prime_field_inverse(cls, a):
        
        if a == 0:
            raise ValueError("0 has no inverse in prime field")
        return int(cls.GFp(int(a))**-1)
    
    @classmethod
    def _flatten_add(cls, expr):
        
        if isinstance(expr, SympyAdd):
            terms = []
            for arg in expr.args:
                terms.extend(cls._flatten_add(arg))
            return terms
        else:
            return [expr]


#------------------------------------------------------------ cut line
def hamming_weight(x):
    """
    count Hamming Weight    (Brian Kernighan)
    """
    count = 0
    while x:
        x &= x - 1
        count += 1
    return count
#------------------------------------------------------------ cut line
import gc
import sys
def clean_memory():
    gc.collect()  
    if hasattr(sys, 'getobjects'):
        gc.collect()