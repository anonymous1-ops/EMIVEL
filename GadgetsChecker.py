# Third-party library

from sympy import postorder_traversal,symbols,flatten,Add
from sympy.logic.boolalg import Xor
from alive_progress import alive_it,alive_bar
from bidict import bidict
from multiprocessing import Pool,cpu_count
import psutil



# Built-in library
from itertools import tee
from re import escape,compile
from argparse import ArgumentParser
import os
import time

# Local file.
from auxiliary import ET,flatten_sympy,sympyGF2N,sympyGFp
import Parameters
import GadgetsAnalysis
import MIA

class checkGadget():
    """ 
    runtime parameters.
    """
    # MIA
    small_number = 0.000000001
    MImatrix=dict()
    # Pr
    probability="f"
    probaLoop=1

    # basic info
    t=-1
    model=""
    model_str=""
    detail="f"
    detail_map={"t":1,"f":0}
    tech="both"
    tech_map={"mi":0,"static":1,"both":2}
    abort="f"
    abort_map={"t":1,"f":0}
    robust=0
    #opt="f"
    #opt_map={"t":1,"f":0}
    maxRow=-1   
    toFile="t"
    toFile_map={"t":1,"f":0}
    logic=True
    para=False
    para_dict={}    


    secrets,len_secrets=list(),0
    shares,len_shares=list(),0       
    shares_op,len_shares_op=list(),0    
    randoms=set()
    invert=set()
    Bits=0
    shareNum=0
    
    # checking
    overload_sympyeval=None
    variable_template = rf'(?<!\w){{}}(?!\w)'
    compiled_patterns_random =None
    compiled_patterns_invert =None
    checklist=list()
    row2Probe={}
    OutputProbe,len_OutputProbe={},0
    inProbe,len_inProbe=[],0
    checksize=0
    
    shares_set=[]
    bits_sharesNum=0

    funcMapping={}
    funcMapping_index={}
    funcMapping_index_op={}
    
    observation_cache=dict()

    max_hours=12
    max_mem = 5


    # muticore
    mcore=0

    # runtime check info
    secure=None
    row=-1
    R=[]
    P_origin=[]
    O=[]
    #num=[]
    P=[]
    P_pr=dict()
    t_in=0
    O_in=[]
    O_inIndex=set()
    O_out=[]
    t_out=0
    O_outIndex=set()
    #opttuple=()
    
    
    def __init__(self,gadget):
        self.gadget=gadget
        self.MI=MIA.MIA(self)
    def clearCheck(self):
        self.secure=None
        self.row=-1
        self.R=[]
        self.R_origin=[]
        self.O=[]
        self.P=[]
        self.P_pr=dict()
        self.t_in=0
        self.O_in=[]
        self.O_inIndex=set()
        self.O_out=[]
        self.t_out=0
        self.O_outIndex=set()
    # Observations Algorithm.
    def initializing(self):
        self.MI.initializing()
        self.t=self.gadget.checkOptions["threshold"]
        model=self.gadget.checkOptions["security"]
        self.model_str=model
        self.tech=self.tech_map[self.gadget.checkOptions["tech."]]
        robust=self.gadget.checkOptions["robust"]
        if("glitch" in robust and "transition" in robust):
            self.robust=3
        elif("glitch" in robust):
            self.robust=1
        elif("transition" in robust):
            self.robust=2
        elif("transitionxor" in robust):
            self.robust=4
        elif("hw" in robust):
            self.robust=5
        from galois import GF
        GF_field = GF(self.gadget.field)
        if GF_field.characteristic == 2 and GF_field.degree > 1:
            self.overload_sympyeval = sympyGF2N()
        else:
            self.overload_sympyeval = sympyGFp()
        self.overload_sympyeval.set_field(GF_field)
        self.abort=self.abort_map[self.gadget.checkOptions["abort"]]
        self.detail=self.detail_map[self.gadget.checkOptions["detail"]]
        self.toFile=self.toFile_map[self.gadget.checkOptions["toFile"]]
        self.mcore=self.gadget.checkOptions["mcore"]
        self.max_hours=self.gadget.checkOptions["maxhours"]
        self.max_mem=self.gadget.checkOptions["maxmem"]
        self.logic=self.gadget.logic
        self.para=self.gadget.para
        self.secrets=self.gadget.secrets
        self.len_secrets=len(self.secrets)
        self.OutputProbe=self.gadget.observationsOutput
        self.len_OutputProbe=len(self.gadget.observationsOutput)
        self.inProbe=self.gadget.observationsIn
        self.len_inProbe=len(self.gadget.observationsIn)
        self.row2Probe=self.gadget.mapRow2Obs
        self.probability=self.gadget.probability
        self.probaLoop=int(self.gadget.probaLoop)
        self.randoms=self.gadget.randoms
        self.compiled_patterns_random = {random: compile(self.variable_template.format(escape(random))) for random in map(str,self.randoms)}
        self.invert=self.gadget.invertible
        self.compiled_patterns_invert = {invert: compile(self.variable_template.format(escape(invert))) for invert in map(str,self.invert)}
        self.Bits=self.gadget.bits
        self.shareNum=self.gadget.shareNum
        self.checklist=self.gadget.observationsCheck
        self.checksize=self.gadget.checksize
        self.O_inIndex=self.gadget.shareIndex
        
        #------------------------------------------------------------------------
        # inputs
        sharesIn=self.gadget.secretsInputs
        sharesInBits=self.gadget.secretsInputsBits
        self.bits_sharesNum=self.Bits*self.shareNum
        #------------------------------------------------------------------------
        if(model == "probing"):
            sharesIn=self.gadget.secrets
            sharesInBits=self.gadget.secretsBits
            self.bits_sharesNum=self.Bits
        self.shares=sharesInBits if self.Bits > 1 else sharesIn
        self.len_shares=len(self.shares)
        self.shares_set=set(self.shares)
        self.len_shares_set=len(self.shares_set)
        self.len_secrets= self.len_shares_set//self.bits_sharesNum if self.len_secrets==0 else self.len_secrets
        # outputs
        sharesOut=self.gadget.secretsOutputs
        sharesOutBits=self.gadget.secretsOutputsBits
        #------------------------------------------------------------------------
        self.shares_op=sharesOutBits if self.Bits > 1 else sharesOut
        self.len_shares_op=len(self.shares_op)
        # mapping
        self.funcMapping = {id: id // self.bits_sharesNum for id in range(self.len_shares)}   
        if(not self.funcMapping):
            raise RuntimeError("probably no secret.")
        firstIndex=min(self.O_inIndex)
        self.funcMapping_index = {id: ((id // self.Bits)%self.shareNum)+firstIndex for id in range(self.len_shares)}  
        self.funcMapping_index_op = {id: ((id // self.Bits)%self.shareNum)+firstIndex for id in range(self.len_shares_op)}  
        if(isinstance(self.mcore,int) and self.mcore>cpu_count()):
            from warnings import warn
            warn("YOU DONNOT HAVE %s CORE!" %(self.mcore))
            self.mcore=cpu_count()
        self.model=getattr(self, model, None)
        self.MImatrix=dict()
        self.observation_cache=dict()

    
    def verify_bool(self): 
        '''
            Test and simplify.
        '''
        
        randoms = sorted(map(str,self.randoms))
        # --------------------------------------------------------------------------------------
        
        
        secondIfR=set()
        count=0

        while(True):
            if(self.model()):
                return True
            count+=1
            
            Rs_num_all=[{random: len(self.compiled_patterns_random[random].findall(i)) for random in randoms} for i in map(str, self.P)]   
            Rs_num={r:sum(r_num[r] for r_num in Rs_num_all) for r in randoms}  

            # first-if
            firstIf={k: v for k, v in Rs_num.items() if v == 1}

            skip_to_next_while_first = False
            for r in firstIf:
                atom=symbols(r)
                for index_expr,expr in enumerate(self.P): 
                    
                    if(Rs_num_all[index_expr][r]==0):
                        continue
                    for el in postorder_traversal(expr):
                        if(isinstance(el,Xor) and atom in el.args):
                            self.P[index_expr]=expr.xreplace({atom:el})
                            
                            skip_to_next_while_first = True  
                            break
                    if skip_to_next_while_first:
                        break
                if skip_to_next_while_first:
                    break

            if skip_to_next_while_first:
                continue  
                    
            
            
            # second-if
            secondIf={k: v for k, v in Rs_num.items() if v > 1}
            secondIf=set(secondIf)-secondIfR
            skip_to_next_while_second = False
            
            for r in secondIf:
                atom=symbols(r)
                sub=False
                beforeNotSub=[]
                for index_expr,expr in enumerate(self.P): 
                    
                    if(Rs_num_all[index_expr][r]==0):
                        continue
                    if(sub):
                        self.P[index_expr]=expr.xreplace(sub)
                        
                        continue
                    for el in postorder_traversal(expr):
                        
                        if(isinstance(el,Xor)):
                            items=set(el.args)
                            if(atom in items and len(self.compiled_patterns_random[str(atom)].findall(str(items)))==1):
                                sub={atom:el}
                                self.P[index_expr]=expr.xreplace(sub)
                                secondIfR.add(str(atom))
                                skip_to_next_while_second = True 
                                for second in beforeNotSub:  
                                    self.P[second[0]]=second[1].xreplace(sub)
                                break
                    else:
                        beforeNotSub.append((index_expr,expr))
                        continue
                if(skip_to_next_while_second):
                    break
            if(skip_to_next_while_second):
                continue
            break
        return False
    
    def verify(self): 
        '''
            Test and simplify.
        '''
        if(self.logic): 
            return self.verify_bool()
        randoms = sorted(map(str,self.randoms))
        # --------------------------------------------------------------------------------------
        secondIfR=set()

        count=0
        
        while(True):
            if(self.model()):
                return True
            count+=1
            
            Rs_num_all=[{random: len(self.compiled_patterns_random[random].findall(i)) for random in randoms} for i in map(str, self.P)]   
            Rs_num={r:sum(r_num[r] for r_num in Rs_num_all) for r in randoms}   

            # first-if
            firstIf={k: v for k, v in Rs_num.items() if v == 1}
            skip_to_next_while_first = False
            for r in firstIf:
                atom=symbols(r)
                for index_expr,expr in enumerate(self.P): 
                    if(Rs_num_all[index_expr][r]==0):
                        continue
                    for el in postorder_traversal(expr):
                        if(isinstance(el,Add)):
                            if(atom in el.args):
                                self.P[index_expr] = self.overload_sympyeval.xreplace(expr,{atom:el})
                            elif(-atom in el.args):
                                self.P[index_expr] = self.overload_sympyeval.xreplace(expr,{atom:el})
                            else:
                                continue
                            skip_to_next_while_first = True 
                            break
                    if skip_to_next_while_first:
                        break
                if skip_to_next_while_first:
                    break

            if skip_to_next_while_first:
                continue  
                    
            # second-if
            
            secondIf={k: v for k, v in Rs_num.items() if v > 1}
            secondIf=set(secondIf)-secondIfR
            skip_to_next_while_second = False
            
            for r in secondIf:
                atom=symbols(r)
                
                sub=False
                beforeNotSub=[]
                for index_expr,expr in enumerate(self.P): 
                    
                    if(Rs_num_all[index_expr][r]==0):
                        continue
                    if(sub):
                        self.P[index_expr]=self.overload_sympyeval.xreplace(expr,sub)
                        
                        continue
                    for el in postorder_traversal(expr):
                        
                        if(isinstance(el,Add)):
                            items=set(el.args)
                            
                            if(atom in items and len(self.compiled_patterns_random[str(atom)].findall(str(items)))==1):
                                sub={atom:el}
                            elif(-atom in items and len(self.compiled_patterns_random[str(atom)].findall(str(items)))==1):
                                sub={-atom:el}
                            else:
                                continue
                            self.P[index_expr]=self.overload_sympyeval.xreplace(expr,sub)
                            
                            secondIfR.add(str(atom))
                            skip_to_next_while_second = True  
                            for i in beforeNotSub:  
                                self.P[i[0]]=self.overload_sympyeval.xreplace(i[1],sub)
                            break
                    else:
                        beforeNotSub.append((index_expr,expr))
                        continue
                if(skip_to_next_while_second):
                    break
            if(skip_to_next_while_second):
                continue
            break
        return False

    def O2p(self):
        """
            Processing the observation.
            0. if with probability, extracting probability to P_pr.
            1. Find out how many outputs intermediate (plus outputs index) and internal intermediate.
            2. The actual checking intermediate set is P.
        """
        O=self.O 
        O=flatten(O) if self.robust in {2,3,4} else O  
        row=[]
        # --------------------------------------------------------------------------------------
        for probe in O:
            
            row.append(probe)
            if probe in self.OutputProbe:
                self.t_out+=1
                output = self.OutputProbe[probe]
                self.P.extend(self.row2Probe[output])
                self.O_out.append(probe)
                if(self.model_str=="pini"):
                    self.O_outIndex.add(self.funcMapping_index_op[self.shares_op[probe]])
                    
            else:
                self.t_in+=1
                internal = self.row2Probe[probe]
                self.P.extend(internal)
                self.O_in.append(probe)
        
        if(self.t_in+self.t_out>self.t):  

            self.t_in=max(0, self.t - self.t_out)
        
        if(self.robust==4): 
            self.P=[Xor(*self.P)] if self.logic else [self.overload_sympyeval.add(*self.P)]
            
        elif(self.probability!="f"):
            keys, values = zip(*[(k, v) for d in self.P for k, v in d.items()])
            self.P, self.P_pr = list(keys), dict(enumerate(values))
        
        self.row=row
        return True

    # Check Algorithm
    def check(self): 
        '''
            Check an O.
        '''
        # --------------------------------------------------------------------------------------
        # Processing observation.
        if(not self.O2p()):
            raise RuntimeError("Error in O2p.")
        verify="check" 
        mi=0
        row =tuple(self.row)
        if(self.probability=="f"):
            cache=tuple(sorted(map(str,self.P)))
           
            if(cache in self.observation_cache):  
               
                if(self.observation_cache[cache]=="?" or self.observation_cache[cache]>self.small_number):
                    self.gadget.obs_mi[row]=self.observation_cache[cache]
                    return False  
                else:
                    return True
        else:
            cache="cache"
        if(self.tech==0):
            mi=self.MI.computingMI()
            if(mi>self.small_number):
                verify=False
        elif(self.tech==1):
            verify=self.verify()
            if(not verify):
                mi="?"
        elif(self.tech==2):
            
            verify=self.verify()
            
            if(not verify):
                mi=self.MI.computingMI()
                if(mi<self.small_number):
                    verify=True
                    mi=0

        
        if not verify:
            
            if(mi == "?"):
                self.gadget.obs_mi[row] = mi
                self.observation_cache[cache] = mi
                
                if(self.para == 1):
                    if(self.detail):
                        print("leak: %s with mi metric = %s".rjust(50, "-") % (row, mi))
                        print("P: %s ".rjust(50, "-") % self.P)
                    
                    if(self.abort):
                        return None
            elif(isinstance(mi, (int, float)) and mi > 0):
                self.gadget.obs_mi[row] = mi
                self.observation_cache[cache] = mi
                
                
                if self.para == 1:
                    if(mi > 0):
                        self.MImatrix[mi] = self.MImatrix.get(mi, 0) + 1
                    if(self.detail):
                        print("leak: %s with mi metric = %s".rjust(50, "-") % (row, mi))
                        print("P: %s ".rjust(50, "-") % self.P)
                    
                    if(self.abort):
                        return None
        return verify

    def bitwisecheck(self,probe): 
        '''
            Check an O.
        '''
        # --------------------------------------------------------------------------------------
        
        MI_para=0
        for temp in probe:
            self.clearCheck()
            self.O=temp
            temp=tuple(sorted(map(str,temp)))
            if(temp not in self.gadget.paraCheck):
                
                verify = self.check()
                if(verify==False):
                    
                    row =tuple(self.row)
                    mi=self.gadget.obs_mi[row]
                    self.gadget.paraCheck[temp]=mi
                    if(mi!="?" and mi >0):
                        MI_para+=mi
                    
                elif(verify==True):
                    self.gadget.paraCheck[temp]=0
            else:
                mi=self.gadget.paraCheck[temp]
                if(mi!="?" and mi >0):
                    MI_para+=mi
            
       
        MI_para=MI_para/self.para
        if(MI_para>0):
            self.MImatrix[MI_para] = self.MImatrix.get(MI_para, 0) + 1
            
            if(self.abort):
                return None
            return False
        else:
            return True

    def probing(self):
        '''
            Test probing security.
        '''

        p=self.P
        t1_t2=0 

        # --------------------------------------------------------------------------------------
        leakSecrets=[set() for _ in range(self.len_secrets)]

        for o in p:
            checkShares=o.free_symbols & self.shares_set
            for cS in checkShares:
                leakSecrets[self.funcMapping[self.shares[cS]]].add(self.funcMapping_index[self.shares[cS]])
            if(max(map(len, leakSecrets))>t1_t2):
                return False
        return True

    def ni(self):
        '''
            Test NI.
        '''
        p=self.P
        t1_t2=self.t
        # --------------------------------------------------------------------------------------
        leakShares=[set() for _ in range(self.len_secrets)]
        for o in p:
            checkShares=o.free_symbols & self.shares_set
            for cS in checkShares:
                leakShares[self.funcMapping[self.shares[cS]]].add(self.funcMapping_index[self.shares[cS]])
            if(max(map(len, leakShares))>t1_t2):
                return False
        return True

    def sni(self):
        '''
            Test SNI.
        '''
        p=self.P
        t=self.t_in
        # --------------------------------------------------------------------------------------
        leakShares=[set() for _ in range(self.len_secrets)]
        for o in p:
            checkShares=o.free_symbols & self.shares_set
            for cS in checkShares:
                leakShares[self.funcMapping[self.shares[cS]]].add(self.funcMapping_index[self.shares[cS]])
            if(max(map(len, leakShares))>t):
                return False
        return True

    def pini(self):
        '''
            Test PINI.
        '''
        
        safeIndex=self.O_outIndex
        p=self.P

        # --------------------------------------------------------------------------------------

        leakShares=set()
        for o in p:
            checkShares = o.free_symbols & self.shares_set
            for cS in checkShares:
                leakShares.add(self.funcMapping_index[self.shares[cS]])
            if(len(leakShares.difference(safeIndex))>self.t_in):
                return False
        return True

    def checkObs_limits(self):
        process = psutil.Process()
        start_time = time.time()
        max_seconds = self.max_hours * 3600
        max_mem=self.max_mem*1000
        #peak_mem=0  # peak
        processed_count = 0
        checkBar = alive_it(self.checklist, total=self.checksize) if self.probaLoop==1 else self.checklist
        for probe in checkBar:
            try:
                self.clearCheck()
                self.O = probe
                overdue = time.time() - start_time
                if overdue > max_seconds:
                    print(f"⏱️ Over {self.max_hours} hour, processed {processed_count}/{self.checksize}")
                    return processed_count
                
                current_mem = process.memory_info().rss / (1024**2)
                #peak_mem = max(peak_mem, current_mem)
                
                if current_mem > max_mem:
                    print(f"⚠️ memory over {self.max_mem} GB, processed {processed_count}/{self.checksize} ")
                    return processed_count

                
                if(self.para==1):
                    result = self.check()
                elif(self.para>1):
                    result = self.bitwisecheck(probe)
                if result is None:
                    print(f"❌ ends when fail, processed {processed_count}/{self.checksize} ")
                    return processed_count
                processed_count += 1
            except Exception as e:
                print(f"❌ error: {e}, processed {processed_count}/{self.checksize} ")
                import traceback
                traceback.print_exc()  
                return processed_count
        return processed_count
    
    
    # multiprocessing
    def check_mp(self): 
        '''
            Check an O.
        '''
        if(not self.O2p()):
            raise RuntimeError("Error in O2p.")
        verify="check" 
        mi=0
        row =tuple(self.row)
        if(self.probability=="f"and self.para==1):
            cache=tuple(sorted(map(str,self.P)))
            if(cache in self.observation_cache):  
                if(self.observation_cache[cache]=="?" or self.observation_cache[cache]>self.small_number):
                    return [False,(row,self.observation_cache[cache],"cache")]  
                else:
                    return [True,(row,self.observation_cache[cache],"cache")]  
        else:
            cache="cache"
        if(self.tech==0):
            mi=self.MI.computingMI()
            if(mi>self.small_number):
                verify=False
        elif(self.tech==1):
            verify=self.verify()
            if(not verify):
                mi="?"
        elif(self.tech==2):
            verify=self.verify()
            if(not verify):
                mi=self.MI.computingMI()
                if(mi<self.small_number):
                    verify=True
                    mi=0
        if(not verify):
            if(self.para==1 and self.abort):
                verify= None
        return [verify,(row,mi,cache)]

    def bitwisecheck_mp(self,probe): 
        '''
            Check an O.
        '''
        # --------------------------------------------------------------------------------------
        # Processing observation.
        verify="check"
        MI_para_cache=[]
        MI_para=0
        for temp in probe:
            self.clearCheck()
            self.O=temp
            temp=tuple(sorted(map(str,temp)))
            if(temp not in self.gadget.paraCheck):
                verify = self.check_mp()
                if(not verify[0]):
                    mi=verify[1][1]
                    MI_para_cache.append((temp,mi))
                    if(mi!="?" and mi >0):
                        MI_para+=mi
                else:
                    MI_para_cache.append((temp,0))
            else:
                mi=self.gadget.paraCheck[temp]
                if(mi!="?" and mi >0):
                    MI_para+=mi
            

        
        if(MI_para>0):
            if(self.abort):
                return [None,(probe,MI_para,MI_para_cache)]
            return [False,(probe,MI_para,MI_para_cache)]
        else:
            return [True,(probe,MI_para,MI_para_cache)]
  
    processed_count=0
    def checkObs_mp_limits(self,item,start_time=None):
        '''
            check every observation.
        '''
        process = psutil.Process(os.getpid())  
        max_seconds = self.max_hours * 3600  
        max_mem = self.max_mem * 1000  
        #peak_mem=0  # peak
        model=self.gadget.checkOptions["security"]
        #------------------------------------------------------------------------
        self.clearCheck()
        self.O=item
        self.model=getattr(self, model, None)
        if(self.para==1):
            result=self.check_mp()
        elif(self.para>1):
            result = self.bitwisecheck_mp(item)
        
        mem_after = process.memory_info().rss / (1024**2)
        #peak_mem = max(peak_mem, mem_after)
        overdue = time.time() - start_time
        if(result[0]==None):
            print(f"❌ ends when fail.")
        elif overdue > max_seconds:
            print(f"⏱️ Over {self.max_hours} hours.")
            result[0]=None
        elif mem_after > max_mem:
            print(f"⚠️ memory over {self.max_mem} GB")
            result[0]=None
        return result
    

    def callback_mp(self,results,pool,bar):
        if(results[0]==None):
            pool.terminate()
        if(results[1][1]=="?"):
            self.gadget.obs_mi[results[1][0]]=results[1][1]
            if(self.para>1):
                self.observation_cache[results[1][2]]=results[1][1]
        elif(results[1][1]>0):
            self.gadget.obs_mi[results[1][0]]=results[1][1]
            if(self.para>1):
                for MI_para_cache in results[1][2]:
                    self.gadget.paraCheck[MI_para_cache[0]]=MI_para_cache[1]
            else:
                self.observation_cache[results[1][2]]=results[1][1]
            self.MImatrix[results[1][1]] = self.MImatrix.get(results[1][1], 0) + 1
        self.processed_count+=1
        bar()
    @staticmethod
    def init_worker(instance):
        instance.initializing()
    def multiprocessing(self):
        start_time = time.time()  
        with alive_bar(self.checksize) as bar:
            with Pool(processes=self.mcore, initializer=self.init_worker, initargs=(self,)) as pool:
                for item in self.checklist:
                    pool.apply_async(self.checkObs_mp_limits,args=(item,start_time),callback=lambda results:self.callback_mp(results,pool,bar))
                pool.close()
                pool.join()
        return self.processed_count

    

    def loop_run(self):
        if(isinstance(self.mcore,int) and self.mcore>0):
            processed_count=self.multiprocessing()
        else:
            processed_count=self.checkObs_limits()
        top_d_mi = []
        if(processed_count==self.checksize):
            if(self.gadget.obs_mi):
                if(self.MImatrix):
                    for mi in sorted(self.MImatrix.keys(), reverse=True):
                        count = self.MImatrix[mi]
                        needed = min(self.t - len(top_d_mi), count)
                        top_d_mi.extend([mi] * needed)
                        if len(top_d_mi) >= self.t:
                            break
        else:
            raise RuntimeError(f"❌ Error, processed {processed_count}/{self.checksize}")
        if(not top_d_mi):
            top_d_mi= [0]*self.t
        return top_d_mi
    
    def run(self):
        #------------------------------------------------------------------------
        print("Checking...")
        if(isinstance(self.mcore,int) and self.mcore>0):
            processed_count=self.multiprocessing()
        else:
            processed_count=self.checkObs_limits()
        if(processed_count==self.checksize):
            print(f"complete, processed {processed_count}/{self.checksize} 📌 ")
            if(self.gadget.obs_mi):
                print("💔 Insecure")
                if(self.MImatrix):
                    min_key,max_key = min(self.MImatrix),max(self.MImatrix)
                    min_value,max_value = self.MImatrix[min_key],self.MImatrix[max_key]
                    avg = sum(k * v for k, v in self.MImatrix.items()) / sum(self.MImatrix.values())
                    top_d_mi = []
                    for mi in sorted(self.MImatrix.keys(), reverse=True):
                        count = self.MImatrix[mi]
                        needed = min(self.t - len(top_d_mi), count)
                        top_d_mi.extend([mi] * needed)
                        if len(top_d_mi) >= self.t:
                            break
                    print("min(count): (%s,%s);max(count): (%s,%s);avg: (%s)." %(min_key,min_value,max_key,max_value,avg))
                    print("d max mi (%s)." %(top_d_mi))
            else:
                print("💚 secure")
        else:
            print(f"complete, processed {processed_count}/{self.checksize} 📌 ")
            if(self.gadget.obs_mi and self.MImatrix):
                min_key,max_key = min(self.MImatrix),max(self.MImatrix)
                min_value,max_value = self.MImatrix[min_key],self.MImatrix[max_key]
              
                avg = sum(k * v for k, v in self.MImatrix.items()) / sum(self.MImatrix.values())
                top_d_mi = []
                for mi in sorted(self.MImatrix.keys(), reverse=True):
                    count = self.MImatrix[mi]
                    needed = min(self.t - len(top_d_mi), count)
                    top_d_mi.extend([mi] * needed)
                    if len(top_d_mi) >= self.t:
                        break
                print("min(count): (%s,%s);max(count): (%s,%s);avg: (%s)." %(min_key,min_value,max_key,max_value,avg))
                print("d max mi (%s)." %(top_d_mi))
        if(self.toFile and self.checksize>0):
            self.gadget.saveToFile()
            
        from datetime import datetime
        print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        return True

    
# cmd Algorithm.
def parseArgs():
    '''
        User commands.
    '''
    parser = ArgumentParser(description="Making checker's args.")
    # basic
    parser.add_argument("-p","--path",          metavar="/gadgets/...",                     required=True,                                          help = "The path of the gadget file.")
    parser.add_argument("-m","--model",         metavar="ni, sni, pini, ...",               required=True,                                          nargs=1,choices=["ni","sni","pini","probing","fni","rpc","rpe","rps","rrpe","mirpe"],       help = "The security models to check.")
    parser.add_argument("-r","--robust",        metavar="glitch, transition, ...",          nargs="+",choices=["glitch","transition","transitionxor","hw"],              default=[],                                                            help = "The robust-extend of the probing attack model.")  
    parser.add_argument("-t","--threshold",     metavar="1, 2, ...",                        required=True,                                          type=int,                                                                                   help = "The probing-threshold of the probing attack model.")
      
    
    # r-p model
    #parser.add_argument("-c","--coefficient",   metavar="1, 2, ...",                        help = "The max coefficient of the random probing attack model.",                                   type=int)
    #parser.add_argument("-cs","--conditions",   metavar="[[0],[1],[0,1]]",                  help = "The verification conditions of random probing security model.",                             type=list)
    
    # optional
    parser.add_argument("--tech",               metavar="MI or static or both",             nargs=1,choices=["mi","static","both"],                         default="both",                             help = "If need to compute MI only without static type checking.")
    parser.add_argument("--abort",              metavar="t or f",                           nargs=1,choices=["t","f"],                                      default="f",                                help = "If need to stop when finding an insecure observation.")
    parser.add_argument("--detail",             metavar="t or f",                           nargs=1,choices=["t","f"],                                      default="f",                                help = "If need to print details.")
    parser.add_argument("--tofile",             metavar="t or f",                           nargs=1,choices=["t","f"],                                      default="t",                                help = "If need to write insecure observation and its MI to file.")
    parser.add_argument("--mcore",              metavar="1, 2, ...",                        type=int,                                                       default=0,                                  help = "Number of cores.")  
    parser.add_argument("--maxhours",           metavar="1, 2, ...",                        type=int,                                                       default=12,                                 help = "max hours.")  
    parser.add_argument("--maxmem",             metavar="1, 2, ...",                        type=int,                                                       default=5,                                  help = "max memory.") 
    args = parser.parse_args()                                              
    return args
@ET
def loop_maskingChecker(gadget):
    '''
        Check if masking is secure.
    '''
    gadget.probaLoop=int(gadget.probaLoop)
    # --------------------------------------------------------------------------------------
    print("Checking [loop = (%s)]..." %(gadget.probaLoop))
    checkBar = alive_it(range(gadget.probaLoop), total=gadget.probaLoop)
    loop_top_d_mi= [0] * int(gadget.checkOptions["threshold"])
    Cgadget=checkGadget(gadget)
    for _ in checkBar:
        GadgetsAnalysis.analysisGadget(gadget).probing()
        Cgadget.initializing()
        top_d_mi=Cgadget.loop_run()
        for i in range(Cgadget.t):
            loop_top_d_mi[i] += top_d_mi[i]
        
    if(not any(loop_top_d_mi)):
        print("💚 secure")
        
    else:
        print("💔 Insecure")
        print("[loop = (%s)] -> d max mi (%s)." %(Cgadget.probaLoop,[x / Cgadget.probaLoop for x in loop_top_d_mi]))
    from datetime import datetime
    print(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    return True
@ET
def maskingChecker():
    '''
        Check if masking is secure.
    '''
    gadget=Parameters.gadget( 
            name="",
            expressions=[],
            mapGates={"&":0,"^":0,"~":0,"+":0,"*":0,"-":0},
            mapRow2exp=bidict(),
            mapRow2Obs={},
            encodingRow=[],
            secrets=(),
            secretsBits=(),
            secretsInputs=(),
            secretsInputsBits=(),
            secretsOutputs=(),
            secretsOutputsBits=(),
            invertible=(),
            shareNum=0,
            shareIndex=(),
            randoms=(),
            probability="f",
            probaLoop=1,
            para=1,
            bits=1,
            field=2,
            logic=True,
            
            observationsIn=[],
            observationsOutput={},
            observationsCheck=[],
            checksize=0,
            paraCheck={},
            reg={},
            rpcoeff=[],
            obs_mi={},
            
            checkOptions={"path":"","security":"","robust":[],"tech.":"","abort":"","detail":"","toFile":"","mcore":1,"maxhours":12,"maxmem":5,"threshold":-1}
            )
    # --------------------------------------------------------------------------------------
    args=parseArgs()
    gadget.checkOptions=dict(zip(gadget.checkOptions, [args.path,args.model[0],args.robust,args.tech[0],args.abort[0],args.detail[0],args.tofile[0],args.mcore,args.maxhours,args.maxmem,args.threshold]))
    print("Analyzing...")
    GadgetsAnalysis.analysisGadget(gadget).analysis()
    gadget.printParams()
    if(int(gadget.probaLoop)>1):
        return loop_maskingChecker(gadget)
    Cgadget=checkGadget(gadget)
    print("Initializing...")
    Cgadget.initializing()
    Cgadget.run()
    return True


if __name__=="__main__":
    maskingChecker()