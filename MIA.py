# TPL
from sympy import Symbol,Expr,srepr,flatten
from sympy.logic.boolalg import Boolean,Not,sympify
from sympy.utilities.iterables import ibin
from math import log2,prod
from itertools import combinations,product
from galois import GF
import numpy as np
import re
from collections import Counter

# Local files.
import auxiliary

class MIA():
    """ 
    Some runtime check parameters.
    """
    small_number = 0.00000000001

    MI_norm=1   
    probability="f"
    model=None
    model_str=""
    HW=False
    func="CMI"
    para=1
    allIndex=[]
    Bits=0
    Arithmetic={"field":2,"GF_field":None,"logic":True}
    NegativeOne={sympify("-1")}
    secrets,len_secrets={},0
    shares={}
    shares_set={}
    shares_op={}
    sharesNum=0
    OutputProbe=set()
    funcMapping={}
    funcMapping_index={}
    funcMapping_index_op={}
    randoms=set()

    atomsInp=set()
    freeSymbolsInp=set()
    numInp=set()
    mayLeak=[]
    condition=[]
    def __init__(self,checkGadget):
        self.gadget=checkGadget.gadget
        self.Cgadget=checkGadget
    # Initializing
    def initializing(self):
        self.Bits=self.gadget.bits
        self.Arithmetic["field"]=self.gadget.field
        self.Arithmetic["GF_field"] = GF(self.Arithmetic["field"])
        self.Arithmetic["logic"]=self.gadget.logic
        if("hw" in self.gadget.checkOptions["robust"]):
            self.HW=True
        self.sharesNum=self.gadget.shareNum
        self.allIndex=self.gadget.shareIndex
        self.secrets=self.gadget.secrets
        self.len_secrets=len(self.secrets)
        self.randoms=self.gadget.randoms
        self.para=self.gadget.para
        self.probability=self.gadget.probability
        self.model_str=self.gadget.checkOptions["security"]
        if(self.para>1):
            if(self.model_str=="probing"):
                self.MI_norm=self.len_secrets
            elif(self.model_str in ["pini","sni","ni"]):
                self.MI_norm=self.len_secrets*self.sharesNum
        elif(self.para==1):
            if(self.model_str=="probing"):
                self.MI_norm=log2(float(self.gadget.field))*self.len_secrets
            elif(self.model_str in ["pini","sni","ni"]):
                self.MI_norm=log2(float(self.gadget.field))*self.len_secrets*self.sharesNum
        # ----------------------------------------------------------------------------------------------------
        self.OutputProbe=self.gadget.observationsOutput
        if(self.model_str=="probing"):
            self.shares=self.gadget.secretsBits if self.Bits>1 else self.gadget.secrets
            self.shares_set=set(self.shares)
        elif(self.model_str in ["pini","sni","ni"]):
            self.shares= self.gadget.secretsInputsBits if self.Bits>1 else self.gadget.secretsInputs
            self.shares_set=set(self.shares)
            self.funcMapping = {id: id // (self.Bits*self.sharesNum) for id in range(len(self.shares))}    
            self.shares_op=self.gadget.secretsOutputsBits if self.Bits > 1 else self.gadget.secretsOutputs
            firstIndex=min(self.allIndex)
            self.funcMapping_index = {id: ((id // self.Bits)%self.sharesNum)+firstIndex for id in range(len(self.shares))}   
            self.funcMapping_index_op = {id: ((id // self.Bits)%self.sharesNum)+firstIndex for id in range(len(self.shares_op))} 
        self.model=getattr(self, self.model_str, None)
        
    
    def clear(self):
        self.atomsInp=set()
        self.freeSymbolsInp=set()
        self.numInp=set()
        self.mayLeak=[]
        self.condition=[]
    
    def opt_y(self,x,y,z):
        xz_vars = set(x + z)
        vars_list = [expr.free_symbols for expr in y]
        
        
        var_index = {}
        for i, vs in enumerate(vars_list):
            for v in vs:
                var_index.setdefault(v, set()).add(i)
        
        related = set()
        stack = []
        
        
        atomsInp = set()
        freeSymbolsInp = set()
        y_filtered = []
        
        for i, vs in enumerate(vars_list):
            if vs & xz_vars:
                related.add(i)
                stack.append(i)
        
       
        while stack:
            i = stack.pop()
            expr = y[i]
            y_filtered.append(expr)
            atomsInp.update(expr.atoms())
            freeSymbolsInp.update(expr.free_symbols)
            
            for var in vars_list[i]:
                for j in var_index.get(var, set()):
                    if j not in related:
                        related.add(j)
                        stack.append(j)
        
        self.atomsInp = atomsInp
        self.freeSymbolsInp = freeSymbolsInp
        return y_filtered
        
    # Condition MI analysising
    
    def CMI_bool_HW(self, batch_bits=20):
        if not self.probes:
            return 0.0
        y, x, z = list(self.probes), list(self.mayLeak), list(self.condition)
        lenx, leny, lenz = len(x), len(y), len(z)
        xyz = x + y + z

        
        Hxz = len(set(x) | set(z))     
        Hz = lenz

       
        allVars = tuple(set(self.freeSymbolsInp) | set(x) | set(z))
        allVars_len = len(allVars)
        symbol_to_pos = {s: i for i, s in enumerate(allVars)}

        
        public = set(allVars) - self.shares_set - set(self.randoms)
        vals_list = []
        for v in allVars:
            if v in public:
                vals_list.append(np.array([1], dtype=np.uint8))  
            else:
                vals_list.append(np.array([0, 1], dtype=np.uint8))  
        
        vals_len = [len(a) for a in vals_list]
        total_states = np.prod(vals_len)

       
        compiled_exprs = []
        for expr in xyz:
            deps = [symbol_to_pos[s] for s in expr.free_symbols if s in symbol_to_pos]
            code = str(expr)
            for s in expr.free_symbols:
                if s in symbol_to_pos:
                    code = re.sub(rf'\b{re.escape(str(s))}\b', f'v[:,{symbol_to_pos[s]}]', code)
            
            func = eval(f'lambda v: ({code}).astype(int)')
            compiled_exprs.append((func, deps))

        
        batch_size = 1 << batch_bits  
        num_batches = (total_states + batch_size - 1) // batch_size

        
        if(allVars_len <= 64):
                   
            def pack_bits(arr):
                
                arr64 = arr.astype(np.uint64, copy=False)
                powers = (1 << np.arange(arr64.shape[1], dtype=np.uint64))
                return arr64.dot(powers)

            
            counts_xyz_total = Counter()
            counts_yz_total  = Counter()
            mask = 1 << np.arange(allVars_len, dtype=np.uint64)

            
            for bat in range(num_batches):
                start = bat * batch_size
                end = min((bat + 1) * batch_size, total_states)

                
                idxs = np.arange(start, end, dtype=np.uint64)
                vals = np.zeros((end - start, allVars_len), dtype=np.uint8)
                for i, l in enumerate(vals_len):
                    vals[:, i] = vals_list[i][idxs % l]
                    idxs //= l

                xyz_vals = np.column_stack([func(vals) for func, _ in compiled_exprs])

                xyz_hw = np.concatenate([
                    xyz_vals[:, :lenx],       # x
                    xyz_vals[:, lenx:lenx + leny].sum(axis=1, dtype=np.uint64)[:, None],                     # HW(y)
                    xyz_vals[:, lenx + leny:] # z
                ], axis=1)

                idx_xyz = pack_bits(xyz_hw)
                idx_yz  = pack_bits(xyz_hw[:, lenx:])

                counts_xyz_total.update(idx_xyz.tolist())
                counts_yz_total.update(idx_yz.tolist())
                del vals, xyz_vals, xyz_hw, idx_xyz, idx_yz
        else:
            def pack_bits(arr):
                nrows, nbits = arr.shape
                nchunks = (nbits + 64 - 1) // 64
                out = np.zeros((nrows, nchunks), dtype=np.uint64)
                for i in range(nchunks):
                    s = i*64; e = min(s+64, nbits)
                    sub = arr[:, s:e].astype(np.uint64, copy=False)
                    powers = (1 << np.arange(sub.shape[1], dtype=np.uint64))
                    out[:, i] = sub.dot(powers)
                return out

            
            counts_xyz_total = Counter()
            counts_yz_total  = Counter()
            mask = 1 << np.arange(allVars_len, dtype=np.uint64)

            
            for bat in range(num_batches):
                start = bat * batch_size
                end = min((bat + 1) * batch_size, total_states)

               
                idxs = np.arange(start, end, dtype=np.uint64)
                vals = np.zeros((end - start, allVars_len), dtype=np.uint8)
                for i, l in enumerate(vals_len):
                    vals[:, i] = vals_list[i][idxs % l]
                    idxs //= l

                xyz_vals = np.column_stack([func(vals) for func, _ in compiled_exprs])
                
                xyz_hw = np.concatenate([
                    xyz_vals[:, :lenx],       # x
                    xyz_vals[:, lenx:lenx+leny].sum(axis=1, dtype=np.uint8)[:, None],                     # HW(y)
                    xyz_vals[:, lenx+leny:]   # z
                ], axis=1)

                idx_xyz = pack_bits(xyz_hw)
                idx_yz  = pack_bits(xyz_hw[:, lenx:])

                counts_xyz_total.update([tuple(r) for r in idx_xyz])
                counts_yz_total.update([tuple(r) for r in idx_yz])
                del vals, xyz_vals, xyz_hw, idx_xyz, idx_yz

       
        p_xyz = np.array(list(counts_xyz_total.values()), dtype=float) / total_states
        p_yz  = np.array(list(counts_yz_total.values()), dtype=float) / total_states

        Hxyz = -np.sum(p_xyz[p_xyz > 0] * np.log2(p_xyz[p_xyz > 0]))
        Hyz = -np.sum(p_yz[p_yz > 0] * np.log2(p_yz[p_yz > 0]))

        MI = Hxz + Hyz - Hxyz - Hz
        return float(MI/self.MI_norm)


    def CMI_bool(self, batch_bits=20):

        if not self.probes:
            return 0.0

        y, x, z = list(self.probes), list(self.mayLeak), list(self.condition)
        y=self.opt_y(x,y,z)

        if(not y):
            return 0.0
        lenx, leny, lenz = len(x), len(y), len(z)
        xyz = x + y + z

        Hxz = len(set(x) | set(z))    
        Hz = lenz


        allVars = tuple(set(self.freeSymbolsInp) | set(x) | set(z))
        allVars_len = len(allVars)
        symbol_to_pos = {s: i for i, s in enumerate(allVars)}

        public = set(allVars) - self.shares_set - set(self.randoms)
        vals_list = []
        for v in allVars:
            if v in public:
                vals_list.append(np.array([1], dtype=np.uint8)) 
            else:
                vals_list.append(np.array([0, 1], dtype=np.uint8))  
        
        
        vals_len = [len(a) for a in vals_list]
        total_states = np.prod(vals_len)
        
        compiled_exprs = []
        for expr in xyz:
            deps = [symbol_to_pos[s] for s in expr.free_symbols if s in symbol_to_pos]
            code = str(expr)
            for s in expr.free_symbols:
                if s in symbol_to_pos:
                    code = re.sub(rf'\b{re.escape(str(s))}\b', f'v[:,{symbol_to_pos[s]}]', code)
           
            func = eval(f'lambda v: ({code}).astype(int)')
            compiled_exprs.append((func, deps))


        batch_size = 1 << batch_bits  
        num_batches = (total_states + batch_size - 1) // batch_size


        if(allVars_len <= 64):
            def pack_bits(arr):

                arr64 = arr.astype(np.uint64, copy=False)
                powers = (1 << np.arange(arr64.shape[1], dtype=np.uint64))
                return arr64.dot(powers)
          
            counts_xyz_total = Counter()
            counts_yz_total  = Counter()
            mask = 1 << np.arange(allVars_len, dtype=np.uint64)

           
            for bat in range(num_batches):
                start = bat * batch_size
                end = min((bat + 1) * batch_size, total_states)

                
                idxs = np.arange(start, end, dtype=np.uint64)
                vals = np.zeros((end - start, allVars_len), dtype=np.uint8)
                for i, l in enumerate(vals_len):
                    vals[:, i] = vals_list[i][idxs % l]
                    idxs //= l

                xyz_vals = np.column_stack([func(vals) for func, _ in compiled_exprs])

                idx_xyz = pack_bits(xyz_vals)
                idx_yz  = pack_bits(xyz_vals[:, lenx:])

                counts_xyz_total.update(idx_xyz.tolist())
                counts_yz_total.update(idx_yz.tolist())
                del vals, xyz_vals, idx_xyz, idx_yz
        else:
            def pack_bits(arr):
                nrows, nbits = arr.shape
                nchunks = (nbits + 64 - 1) // 64
                out = np.zeros((nrows, nchunks), dtype=np.uint64)
                for i in range(nchunks):
                    s = i*64; e = min(s+64, nbits)
                    sub = arr[:, s:e].astype(np.uint64, copy=False)
                    powers = (1 << np.arange(sub.shape[1], dtype=np.uint64))
                    out[:, i] = sub.dot(powers)
                return out


            counts_xyz_total = Counter()
            counts_yz_total  = Counter()
            mask = 1 << np.arange(allVars_len, dtype=np.uint64)


            for bat in range(num_batches):
                start = bat * batch_size
                end = min((bat + 1) * batch_size, total_states)


                idxs = np.arange(start, end, dtype=np.uint64)
                vals = np.zeros((end - start, allVars_len), dtype=np.uint8)
                for i, l in enumerate(vals_len):
                    vals[:, i] = vals_list[i][idxs % l]
                    idxs //= l

                xyz_vals = np.column_stack([func(vals) for func, _ in compiled_exprs])

                idx_xyz = pack_bits(xyz_vals)
                idx_yz  = pack_bits(xyz_vals[:, lenx:])

                counts_xyz_total.update([tuple(r) for r in idx_xyz])
                counts_yz_total.update([tuple(r) for r in idx_yz])

                del vals, xyz_vals, idx_xyz, idx_yz


        p_xyz = np.array(list(counts_xyz_total.values()), dtype=float) / total_states
        p_yz  = np.array(list(counts_yz_total.values()), dtype=float) / total_states

        Hxyz = -np.sum(p_xyz[p_xyz > 0] * np.log2(p_xyz[p_xyz > 0]))
        Hyz = -np.sum(p_yz[p_yz > 0] * np.log2(p_yz[p_yz > 0]))


        MI = Hxz + Hyz - Hxyz - Hz
        return float(MI/self.MI_norm)

    
    def CMI_arith_HW(self,batch_bits=20): 
        if(self.Arithmetic["logic"]):
            return self.CMI_bool_HW()
        if(not self.probes):
            return 0

       
        field = self.Arithmetic["field"]
        GF_field = self.Arithmetic["GF_field"]

        y, x, z = list(self.probes), list(self.mayLeak), list(self.condition)


        lenx, leny, lenz = len(x), len(y), len(z)
        xyz = x + y + z


        Hxz = len(set(x) | set(z)) * log2(field)
        Hz = lenz * log2(field)


        allVars = tuple(set(self.freeSymbolsInp) | set(x) | set(z))
        allVars_len = len(allVars)

        public = set(allVars) - self.shares_set - set(self.randoms)
        vals_list = []
        for v in allVars:
            if v in public:
                vals_list.append(np.arange(1, field, dtype=int))  
            else:
                vals_list.append(np.arange(field, dtype=int))      

        vals_len = [len(a) for a in vals_list]


        compiled_exprs = auxiliary.compile_sympy_to_gf(xyz, allVars, GF_field)

        total_states = np.prod(vals_len)
        batch_size = 1 << batch_bits
        num_batches = (total_states + batch_size - 1) // batch_size

        counts_xyz_total = Counter()
        counts_yz_total  = Counter()

        for bat in range(num_batches):
            start = bat * batch_size
            end = min((bat + 1) * batch_size, total_states)
            n = end - start

            idxs = np.arange(start, end, dtype=np.uint64)
            vals = np.zeros((n, allVars_len), dtype=int)
            for i, l in enumerate(vals_len):
                vals[:, i] = vals_list[i][idxs % l]
                idxs //= l

            vals = GF_field(vals)  

            xyz_vals = np.column_stack([f(vals) for f in compiled_exprs])
            xyz_vals = np.array([[int(v) for v in row] for row in xyz_vals])
            

            xyz_HW = np.concatenate([
                xyz_vals[:, :lenx].astype(np.int64),  # x
                np.sum([[bin(int(v)).count('1') for v in row] for row in xyz_vals[:, lenx:lenx+leny]], axis=1, keepdims=True,),  # HW(y) sum
                #np.prod([[bin(int(v)).count('1') for v in row] for row in xyz_vals[:, lenx:lenx+leny]], axis=1, keepdims=True),  # HW(y) prod
                xyz_vals[:, lenx+leny:].astype(np.int64) 
            ], axis=1)

            idx_xyz_tuples = [tuple(int(v) for v in row) for row in xyz_HW]
            idx_yz_tuples  = [tuple(int(v) for v in row[lenx:]) for row in xyz_HW]
            
            counts_xyz_total.update(idx_xyz_tuples)
            counts_yz_total.update(idx_yz_tuples)

            del vals, xyz_vals, xyz_HW, idx_xyz_tuples, idx_yz_tuples


        total = sum(counts_xyz_total.values())
        p_xyz = np.array(list(counts_xyz_total.values()), dtype=float) / total
        p_yz = np.array(list(counts_yz_total.values()), dtype=float) / total

        Hxyz = -np.sum(p_xyz * np.log2(p_xyz))
        Hyz = -np.sum(p_yz * np.log2(p_yz))

        MI = Hxz + Hyz - Hxyz - Hz
        return float(MI/self.MI_norm)
    
    
    def CMI_arith(self,batch_bits=20): 
        if(self.Arithmetic["logic"]):
            return self.CMI_bool()
        if(not self.probes):
            return 0

        field = self.Arithmetic["field"]
        GF_field = self.Arithmetic["GF_field"]

        y, x, z = list(self.probes), list(self.mayLeak), list(self.condition)
        y=self.opt_y(x,y,z)
        if(not y):
            return 0.0
        lenx, leny, lenz = len(x), len(y), len(z)
        xyz = x + y + z
        
        Hxz = len(set(x) | set(z)) * log2(field)
        Hz = lenz * log2(field)


        allVars = tuple(set(self.freeSymbolsInp) | set(x) | set(z))
        allVars_len = len(allVars)


        public = set(allVars) - self.shares_set - set(self.randoms)
        vals_list = []
        for v in allVars:
            if v in public:
                vals_list.append(np.arange(1, field, dtype=int))  
            else:
                vals_list.append(np.arange(field, dtype=int))    

        vals_len = [len(a) for a in vals_list]


        compiled_exprs = auxiliary.compile_sympy_to_gf(xyz, allVars, GF_field)


        total_states = np.prod(vals_len)
        batch_size = 1 << batch_bits
        num_batches = (total_states + batch_size - 1) // batch_size

        counts_xyz_total = Counter()
        counts_yz_total  = Counter()

        for bat in range(num_batches):
            start = bat * batch_size
            end = min((bat + 1) * batch_size, total_states)
            n = end - start

            idxs = np.arange(start, end, dtype=np.uint64)
            vals = np.zeros((n, allVars_len), dtype=int)
            for i, l in enumerate(vals_len):
                vals[:, i] = vals_list[i][idxs % l]
                idxs //= l

            vals = GF_field(vals)  


            xyz_vals = np.column_stack([f(vals) for f in compiled_exprs])
            
            
            idx_xyz_tuples = [tuple(int(v) for v in row) for row in xyz_vals]
            idx_yz_tuples  = [tuple(int(v) for v in row[lenx:]) for row in xyz_vals]

            counts_xyz_total.update(idx_xyz_tuples)

            counts_yz_total.update(idx_yz_tuples)


            del vals, xyz_vals, idx_xyz_tuples, idx_yz_tuples

        total = sum(counts_xyz_total.values())
        p_xyz = np.array(list(counts_xyz_total.values()), dtype=float) / total
        p_yz = np.array(list(counts_yz_total.values()), dtype=float) / total

        Hxyz = -np.sum(p_xyz * np.log2(p_xyz))
        Hyz = -np.sum(p_yz * np.log2(p_yz))



        MI = Hxz + Hyz - Hxyz - Hz
        return float(MI/self.MI_norm)
    

    
    def CMI(self):
        if(self.HW):
            return self.CMI_arith_HW()
        else:
            return self.CMI_arith()
    def CMI_pr(self):
        prAll=list(self.Cgadget.P_pr.values())
        probes=self.Cgadget.P
        # ----------------------------------------------------------------------------------------------------
        lenPs=len(probes)
        nCMI=0
        for choice in ibin(lenPs,"all"): 
            self.Cgadget.P=[probes[i] for i in range(lenPs) if choice[i] == 1]
            pCMI=self.model()   
            pr=prod([pr if c == 1 else 1 - pr for c, pr in zip(choice, prAll)])
            nCMI+=pr*pCMI

        return nCMI

    # security
    def pini(self):
        self.clear()
        safeIndex=set(self.Cgadget.O_outIndex)
        t=self.Cgadget.t_in
        self.probes=set(self.Cgadget.P) if self.probability=="f" else self.Cgadget.P  
        # ----------------------------------------------------------------------------------------------------
        for p in self.probes:
            self.atomsInp.update(p.atoms())
            self.freeSymbolsInp.update(p.free_symbols)
        sharesInp= self.freeSymbolsInp & self.shares_set
        if(not sharesInp):
            return 0
        shares_index_map = {
            s: self.funcMapping_index[self.shares[s]] for s in sharesInp
        }
        PINI_Index = set(shares_index_map.values())

       
        if PINI_Index <= safeIndex:
            return 0

       
        if len(PINI_Index - safeIndex) <= t:
            return 0
        conditions = []
        index_IcutO = list(PINI_Index - safeIndex)

        for index in combinations(index_IcutO, min(len(index_IcutO), t)):
            IplusO = set(index) | safeIndex
            noLeak = [s for s, idx in shares_index_map.items() if idx in IplusO]
            if noLeak:
                conditions.append(set(noLeak))

        if not conditions:
            
            self.mayLeak = sharesInp
            self.condition = []
            return self.CMI()
        

        MI=[]
        for nL in conditions:
            
            self.mayLeak=sharesInp-nL
            self.condition=nL
            
            if(not self.mayLeak):  
                return 0
            

            mi=self.CMI()  

            if(mi<self.small_number):
                return 0
            
            MI.append(mi)

        if(not MI): 
            return 0
        return min(MI)

    
    def probing(self):    
        self.clear()
        self.probes=set(self.Cgadget.P) if self.probability=="f" else self.Cgadget.P 
        # ----------------------------------------------------------------------------------------------------
        for p in self.probes:  
            self.atomsInp.update(p.atoms())
            self.freeSymbolsInp.update(p.free_symbols)
        sharesInp= self.freeSymbolsInp & self.shares_set
        if(not sharesInp):
            return 0
        self.mayLeak,self.condition=sharesInp,set()
        return self.CMI()

    def ni(self):    
        self.clear()
        self.probes=set(self.Cgadget.P) if self.probability=="f" else self.Cgadget.P 
        t=self.Cgadget.t
        # ----------------------------------------------------------------------------------------------------
        

        noLeak=[]
        for p in self.probes:
            self.atomsInp.update(p.atoms())
            self.freeSymbolsInp.update(p.free_symbols)

        sharesInp= self.freeSymbolsInp&self.shares_set
        if(not sharesInp):
            return 0
        NI=[set() for _ in range(self.len_secrets)]
        NI_index=[set() for _ in range(self.len_secrets)]  
        for sh in sharesInp:
            whichSecret=self.funcMapping[self.shares[sh]]
            NI[whichSecret].add(sh)
            NI_index[whichSecret].add(self.funcMapping_index[self.shares[sh]])

        if(max(map(len, NI_index))<=t):
            return 0
        for count,ni in enumerate(NI):
            temp_whichSecret=[]
            shares_index_map = {shares: self.funcMapping_index[self.shares[shares]] for shares in ni}
            whichSecret=len(NI_index[count])
            if(whichSecret<=0):
                continue
            elif(whichSecret<=t):
                noLeak.append([list(ni)])
                continue
            for index in combinations(NI_index[count],min(whichSecret,t)):
                index = set(flatten(index))
                valid_indices = index
                temp = [shares for shares, idx in shares_index_map.items() if idx in valid_indices]
                temp_whichSecret.append(temp)
            noLeak.append(temp_whichSecret)

        noLeak=product(*noLeak)
        
        MI=[]

        for nL in noLeak:
           
            self.mayLeak=sharesInp
            self.condition=set(flatten(nL))
            self.mayLeak=self.mayLeak-self.condition
            
            if(not self.mayLeak):   
                return 0

            mi=self.CMI()  
            if(mi<self.small_number):
                return 0
                MI.append(mi)
            self.condition=self.condition
            
            MI.append(mi)
        if(not MI):
            self.mayLeak=sharesInp
            self.condition=[]
            return self.CMI()
        return min(MI)
        
    def sni(self):
        self.clear()
        t=self.Cgadget.t_in
        self.probes=set(self.Cgadget.P) if self.probability=="f" else self.Cgadget.P 
        # ----------------------------------------------------------------------------------------------------
        
        noLeak=[]
        for p in self.probes:
            self.atomsInp.update(p.atoms())
            self.freeSymbolsInp.update(p.free_symbols)
        sharesInp= self.freeSymbolsInp&self.shares_set
        if(not sharesInp):
            return 0
        SNI=[set() for _ in range(self.len_secrets)]
        SNI_index=[set() for _ in range(self.len_secrets)]  
        for sh in sharesInp:
            whichSecret=self.funcMapping[self.shares[sh]]
            SNI[whichSecret].add(sh)
            SNI_index[whichSecret].add(self.funcMapping_index[self.shares[sh]])
        if(max(map(len, SNI_index))<=t):
            return 0
        for count,sni in enumerate(SNI):
            temp_whichSecret=[]
            shares_index_map = {shares: self.funcMapping_index[self.shares[shares]] for shares in sni}
            whichSecret=len(SNI_index[count])
            if(whichSecret<=0):
                continue
            elif(whichSecret<=t):
                noLeak.append([list(sni)])
                continue
            for index in combinations(SNI_index[count],min(whichSecret,t)):
                index = set(flatten(index))
                valid_indices = index
                temp = [shares for shares, idx in shares_index_map.items() if idx in valid_indices]
                temp_whichSecret.append(temp)
            noLeak.append(temp_whichSecret)
        noLeak=product(*noLeak)

        MI=[]

        for nL in noLeak:

            self.mayLeak=sharesInp
            self.condition=set(flatten(nL))
            self.mayLeak=self.mayLeak-self.condition
            
            if(not self.mayLeak):   
                return 0
            
            mi=self.CMI()  
            if(mi<self.small_number):
                return 0
                MI.append(mi)
            self.condition=self.condition
            MI.append(mi)
        if(not MI): 
            self.mayLeak=sharesInp
            self.condition=[]
            return self.CMI()
        return min(MI)
    
    def computingMI(self):
        if(self.probability!="f"):
            return self.CMI_pr()
        return self.model()

