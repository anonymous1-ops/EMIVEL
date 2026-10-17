# Third-party library
from sympy import sympify,symbols,postorder_traversal,Symbol,Expr,srepr,Integer
from sympy.logic.boolalg import Boolean,Not
from sympy.core.symbol import Symbol
from alive_progress import alive_it
from bidict import bidict

# Built-in library
from itertools import combinations,product,chain
from math import comb

class analysisGadget():
    """
    Analysis phase.
    """
    flag=-1         # with noise

    # initializing parameters
    bits=-1
    #secrets=[]
    sharesIn=[]
    encoding_shares=[]
    sharesOut=[]
    randoms=[]
    encoding_randoms=set()  
    inputs=set()
    hashMap={hash(tuple([1])),hash(tuple([0]))}
    hashMap_row=bidict()

    # checkoptions
    model=None
    model_str=""
    robust=0
    threshold=0
    def __init__(self,gadget):
        # basic info
        self.gadget=gadget  
        
    def ensuringInfo(self):
        """
        check missing info.
        """
        # error 
        if(self.gadget.logic and (self.gadget.mapGates["*"]>1 or self.gadget.mapGates["+"]>1 or self.gadget.mapGates["-"]>1) ):
            raise RuntimeError("bool or arith.?")
        elif(not self.gadget.logic and (self.gadget.mapGates["~"]>1 or self.gadget.mapGates["&"]>1 or self.gadget.mapGates["^"]>1) ):
            raise RuntimeError("bool or arith.?")
        # wrong
        if((not self.gadget.observationsIn and not self.gadget.observationsOutput and not self.gadget.encodingRow) or not self.gadget.observationsCheck):
            #raise UserWarning("NO leakage?")
            from warnings import warn
            warn("NO leakage?")
        
        if(not self.gadget.secrets):
            if(self.gadget.checkOptions["security"]=="probing" ):
                raise RuntimeError("NO secrets.")
            else:
                from warnings import warn
                warn("NO secrets?")
        if(self.gadget.bits>1):
            if(not self.gadget.secretsBits):
                if(self.gadget.checkOptions["security"]=="probing" ):
                    raise RuntimeError("NO secrets.")
                else:
                    from warnings import warn
                    warn("NO secrets?")
            elif(not self.gadget.secretsInputsBits or not self.gadget.secretsOutputsBits):
                raise RuntimeError("different inputs bits.")
        if(not self.gadget.randoms):
            from warnings import warn
            warn("NO randomness?")
        
    
    def initializing(self):
        prob=self.gadget.probability
        try:
            prob=eval(prob) 
            if(prob<=1 and prob>0):   
                self.flag=3
        except:
            if(prob=="t"):  
                self.flag=1
            elif(prob=="random"):   
                self.flag=2
            elif(prob=="f"):
                self.gadget.probability="f"
            else:
                raise RuntimeError("Worng probability parameter.")
        self.bits=self.gadget.bits
        
        self.sharesIn=self.gadget.secretsInputsBits if self.bits>1 else  self.gadget.secretsInputs
        self.sharesOut=self.gadget.secretsOutputsBits if self.bits>1 else  self.gadget.secretsOutputs
        self.randoms=set(self.gadget.randoms)
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
        self.model_str=self.gadget.checkOptions["security"]
        self.threshold=self.gadget.checkOptions["threshold"]
        self.encoding_shares=self.gadget.encodingRow
        for expr in self.gadget.expressions:
            try:
                gate,logic=expr.split("=")
            except: 
                raise RuntimeError("Incorrect expression in ROW: ",self.gadget.mapRow2exp.inverse[expr])
            if("[" in logic and "]" in logic):
                logic=logic[1:-1]
            if("<"in logic):
                logic=logic[:logic.index("<")]
            if(";"in logic):
                logic,_=logic.split(";")
            symLogic=sympify(logic,convert_xor=False)
            rowOfob=self.gadget.mapRow2exp.inverse[expr]
            if(rowOfob in self.gadget.encodingRow):
                self.encoding_randoms.add(symLogic)
        opt_expressions_randoms=set(self.randoms)-set(self.encoding_randoms)
        if(self.gadget.logic):
            for rand in list(opt_expressions_randoms):  
                self.hashMap.add(hash(tuple([rand])))
                self.hashMap.add(hash(tuple([Not(rand)])))
        else:
            for rand in list(opt_expressions_randoms):
                self.hashMap.add(hash(tuple([rand])))
                self.hashMap.add(hash(tuple([-rand])))
        if(self.threshold>1):
            self.inputs=set(self.randoms)-set(self.encoding_randoms) if self.model_str=="probing" else set(self.randoms)-set(self.encoding_randoms) | set(self.sharesIn)
           
    def gen_allObs(self,ObsIn,ObsOut,Trans=False,sharesIn_notrans=[]):
        """
        gen \mathcal{O}
        """
        if(self.flag!=-1):
            from random import random
            ObsIn.extend(self.inputs)
            for p in self.inputs:
                    if(self.flag==1):
                        self.gadget.mapRow2Obs[p]=[{p:float(1)}]
                    elif(self.flag==2):
                        self.gadget.mapRow2Obs[p]=[{p:random()}]
                    elif(self.flag==3):
                        self.gadget.mapRow2Obs[p]=[{p:float(self.gadget.probability)}]
        else:
            ObsIn.extend(self.inputs)
            self.gadget.mapRow2Obs.update({p: [p] for p in self.inputs})
        
        if(Trans==False):
            
            observationsCheck=combinations(list(ObsOut)+ObsIn,self.threshold)
            checksize=comb(len(ObsIn)+len(ObsOut),self.threshold)
        elif(Trans==True):
            observationsCheck=chain(combinations(combinations(list(ObsOut)+ObsIn,2),self.threshold),combinations(sharesIn_notrans,1))
            checksize=comb(comb(len(ObsIn)+len(ObsOut),2),self.threshold)+comb(len(sharesIn_notrans),1)
            
        if(self.gadget.para>1):
            observationsCheck=product(observationsCheck,repeat=self.gadget.para)
            checksize = checksize ** self.gadget.para
        
        self.gadget.observationsIn=ObsIn
        self.gadget.observationsOutput=ObsOut
        self.gadget.observationsCheck=observationsCheck
        self.gadget.checksize=checksize
        return True

    def gadgetInfo(self):
        """
        basic info.
        """
        # --------------------------------------------------------------------------------------
        with open(self.gadget.checkOptions["path"], "r" ) as script:
            row=0
            for item in script.readlines():
                row +=1
                if(item.isspace()): # All blank.
                    continue
                if("#" in item): # Comment.
                    item=item[:item.index("#")]
                item=item.replace("\t","").replace("\n","")
                if(item=="end"): # End.
                    break
                if("=" in item): # Assignment. 
                    if(":=" in item):
                        self.gadget.encodingRow.append(str(row))
                        
                        item = item.replace(":","")
                    expression = item.replace(" ","")
                    self.gadget.expressions.append(expression)
                    self.gadget.mapRow2exp[str(row)]=expression
                    
                    for key in self.gadget.mapGates:
                        self.gadget.mapGates[key]+=expression.count(key)
                    continue
                temp= item.strip(" ").split(" ")
                if(temp[0]=="gadget"):
                    self.gadget.name =temp[-1] 
                elif("secrets" in temp[0]):
                    secrets=symbols(temp[-1].split(","))
                    if("bit" in temp[0]):
                        
                        bits=int(temp[0][0])
                        bits_secrets=[]
                        for s in secrets:
                            for b in range(bits):
                                bits_secrets.append(f"{s}{b}")
                        
                        self.gadget.secretsBits={var: id for id, var in enumerate(symbols(tuple(bits_secrets)))}
                        
                        self.gadget.bits=bits
                    
                    self.gadget.secrets={var: id for id, var in enumerate(secrets)}
                elif("inputs" in temp[0]): 
                    inputs=symbols(temp[-1])
                    indexHead,indexTail=temp[-1].split(":")[0:2]
                    self.gadget.shareIndex=[i for i in range(int(indexHead[-1]),int(indexTail[0]))]  
                    self.gadget.shareNum=len(self.gadget.shareIndex)
                    if("bit" in temp[0]):
                        
                        bits=int(temp[0][0])
                        bits_inputs=[]
                        for i in inputs:
                            for b in range(bits):
                                bits_inputs.append(f"{i}{b}")
                        
                        self.gadget.secretsInputsBits={var: id for id, var in enumerate(symbols(tuple(bits_inputs)))}
                        self.gadget.bits=bits
                    
                    self.gadget.secretsInputs={var: id for id, var in enumerate(inputs)}
                elif("outputs"  in temp[0]): 
                    outputs=symbols(temp[-1])
                    if("bit" in temp[0]):
                        
                        bits=int(temp[0][0])
                        bits_outputs=[]
                        for o in outputs:
                            for b in range(bits):
                                bits_outputs.append(f"{o}{b}")
                        
                        self.gadget.secretsOutputsBits={var: id for id, var in enumerate(symbols(tuple(bits_outputs)))}
                        self.gadget.bits=bits
                    
                    self.gadget.secretsOutputs={var: id for id, var in enumerate(outputs)}
                elif(temp[0]=="randoms"):
                    self.gadget.randoms=symbols(temp[-1])
                elif(temp[0]=="noise"):
                    prob=temp[-1]
                    if("," in prob):
                        prob,self.gadget.probaLoop=prob.split(",")
                    self.gadget.probability=prob
                elif(temp[0]=="field"):
                    self.gadget.field=eval(temp[-1])
                    
                    self.gadget.logic=False
                elif(temp[0]=="para"):
                    self.gadget.para=int(temp[-1])
                elif(temp[0]=="invert"):
                    self.gadget.invertible=symbols(temp[-1])
        
        if(int(self.gadget.probaLoop)>1):
            return True
        return self.probing()
        

    def probing(self):
        
        self.initializing()
        self.gadgetObs()
        self.ensuringInfo()
        return True
    # probing model observations
    ## without Pr.

    def robust_extend_transtional(self):
        """
        glitch and/or transition
        """
        # --------------------------------------------------------------------------------------
        Trans=  True if self.robust in {2,3,4} else False 
        Glitch= True if self.robust in {1,3} else False 
        gates={}
        gates_glitch={}
        ObsIn=[]
        ObsOut={}
        checkBar = alive_it(self.gadget.expressions) if self.gadget.probaLoop==1 else self.gadget.expressions
        for ob in checkBar:
            noGlitch=not Glitch
            glitch=[]
            try:
                gate,logic=ob.split("=")
            except: 
                raise RuntimeError("Incorrect expression in ROW: ",self.gadget.mapRow2exp.inverse[ob])
            if(gate=="reg"):   
                sympy_reg=symbols(logic)
                if(sympy_reg in gates):
                    self.gadget.reg[sympy_reg]=gates[sympy_reg]
                continue
            if("[" in logic and "]" in logic):  
                logic=logic[1:-1]
                noGlitch=True
            if(";" in logic):
                logic,temp=logic.split(";")
                glitch.extend(sympify(temp.split(","),convert_xor=False))
            rowOfob=self.gadget.mapRow2exp.inverse[ob]   
            if(self.model_str!="probing" and rowOfob in self.encoding_shares):    
                continue
            sympy_gate=symbols(gate)
            if(logic):
                sympy_logic=sympify(logic,convert_xor=False)
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic  
                    gates_glitch[sympy_gate]=[]
                    continue
                if(noGlitch==False):
                    Notraceback=False 
                    temp=[]
                    for el in postorder_traversal(sympy_logic):
                        if(isinstance(el,Symbol)):
                            if(el in gates):
                                sympy_logic=sympy_logic.xreplace({el:gates[el]})    
                                if(el in self.gadget.reg):
                                    Notraceback=True
                                    protect=self.gadget.reg[el]
                                    if(isinstance(protect,Symbol) or isinstance(protect,Expr) or isinstance(protect, Boolean)):
                                        temp.append(protect)
                                    else:
                                        temp.extend(protect)
                                else:
                                    temp.extend(gates_glitch[el])
                            else:
                                temp.append(el)
                    if(Notraceback):
                        self.gadget.reg[sympy_gate]=temp
                    glitch.extend(temp)
                elif(noGlitch==True):  
                    for el in postorder_traversal(sympy_logic):
                        if(isinstance(el,Symbol) and el in gates):
                            sympy_logic=sympy_logic.xreplace({el:gates[el]})
                    glitch.append(sympy_logic)
                    self.gadget.reg[sympy_gate]=sympy_logic
                gates[sympy_gate]=sympy_logic  
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic  
                    gates_glitch[sympy_gate]=[]
                    continue
                elif(self.inputs and sympy_gate==sympy_logic and sympy_gate in self.inputs):
                    self.inputs.remove(sympy_gate)
            observation=[]
            observation.extend([*glitch])
            if(not observation and not (sympy_logic.atoms()-sympy_logic.free_symbols)):
                raise RuntimeError("Whoops no observation?")
            self.gadget.mapRow2Obs[rowOfob]=observation
            gates_glitch[sympy_gate]=observation
            if(sympy_gate in self.sharesOut):   
                ObsOut[sympy_gate]=rowOfob
                continue
            ObsIn.append(rowOfob)
        sharesIn_notrans=self.encoding_shares if self.model_str=="probing" and Trans else []
        for item in sharesIn_notrans:
            ObsIn.remove(item)
        return self.gen_allObs(ObsIn,ObsOut,Trans,sharesIn_notrans)

    def gadgetObs(self):
        """
        standard
        """
        # --------------------------------------------------------------------------------------
        # probability
        if(self.gadget.probability!="f"):
            self.gadgetObs_pr()
            return True
        # robust.
        elif(self.robust>0):
            self.robust_extend_transtional()
            return True
        gates={}    
        ObsIn=[]    
        ObsOut={}
        checkBar = alive_it(self.gadget.expressions) if self.gadget.probaLoop==1 else self.gadget.expressions
        for ob in checkBar:
            try:
                gate,logic=ob.split("=")
            except: 
                raise RuntimeError("Incorrect expression in ROW: ",self.gadget.mapRow2exp.inverse[ob])
            if(gate=="reg"):   
                self.gadget.reg[logic]=gate
                continue
            if("[" in logic and "]" in logic):  
                logic=logic[1:-1]
            # evaluate observation
            rowOfob=self.gadget.mapRow2exp.inverse[ob]   
            if(self.model_str!="probing" and rowOfob in self.encoding_shares):    
                continue
            sympy_gate=symbols(gate)
            observation=[]
            if(";" in logic):
                logic,extend=logic.split(";")
                observation.extend(sympify(extend.split(","),convert_xor=False))
            
            if(logic):
                sympy_logic=sympify(logic,convert_xor=False)
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic  
                    continue
                for el in postorder_traversal(sympy_logic):
                    if(isinstance(el,Symbol) and el in gates):
                        sympy_logic=sympy_logic.xreplace({el:gates[el]})
                gates[sympy_gate]=sympy_logic 
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic  
                    continue
                elif(self.inputs and sympy_gate==sympy_logic and sympy_gate in self.inputs):
                    self.inputs.remove(sympy_gate)
                observation.append(sympy_logic)
            if(not observation):
                raise RuntimeError("Whoops no observation?")
            self.gadget.mapRow2Obs[rowOfob]=observation
            if(sympy_gate in self.sharesOut):   
                ObsOut[sympy_gate]=rowOfob
                continue
            ObsIn.append(rowOfob)
        return self.gen_allObs(ObsIn,ObsOut,False,[])

    ## with Pr.

    def robust_pr_transtional(self):
        """
        glitch and/or transition with p
        
        """

        if(self.flag==2):
            from random import random
        # --------------------------------------------------------------------------------------
        Trans=  True if self.robust in {2,3,4} else False 
        Glitch= True if self.robust in {1,3} else False 
        gates={}
        gates_glitch={}
        ObsIn=[]
        ObsOut={}
        checkBar = alive_it(self.gadget.expressions) if self.gadget.probaLoop==1 else self.gadget.expressions
        for ob in checkBar:
            noGlitch=not Glitch
            glitch=[]
            gate,logic=ob.split("=")
            if(gate=="reg"):   
                sympy_reg=symbols(logic)
                if(sympy_reg in gates):
                    self.gadget.reg[sympy_reg]=gates[sympy_reg]
                continue
            if("[" in logic and "]" in logic):  
                logic=logic[1:-1]
                noGlitch=True
            if(";" in logic):
                logic,temp=logic.split(";")
                if(self.flag==1):
                    for e in temp.split(","):
                        e,pr=e.split("<")
                        glitch.append({sympify(e,convert_xor=False):float(pr)})
                elif(self.flag==2):
                    for e in temp.split(","):
                        glitch.append({sympify(e,convert_xor=False):random()})
                elif(self.flag==3):
                    prob=self.gadget.probability
                    for e in temp.split(","):
                        glitch.append({sympify(e,convert_xor=False):float(prob)})
            rowOfob=self.gadget.mapRow2exp.inverse[ob]   
            if(self.model_str!="probing" and rowOfob in self.encoding_shares):  
                continue
            sympy_gate=symbols(gate)
            if(logic):
                if(self.flag==1):
                    logic,pr=logic.split("<")
                sympy_logic=sympify(logic,convert_xor=False)
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic 
                    gates_glitch[sympy_gate]=[]
                    continue
                if(noGlitch==False):
                    Notraceback=False 
                    temp=[]
                    for el in postorder_traversal(sympy_logic):
                        if(isinstance(el,Symbol)):
                            if(el in gates):
                                sympy_logic=sympy_logic.xreplace({el:gates[el]})
                                if(el in self.gadget.reg):
                                    Notraceback=True
                                    protect=self.gadget.reg[el]
                                    if(isinstance(protect,Symbol) or isinstance(protect,Expr) or isinstance(protect, Boolean)):
                                        temp.append(protect)
                                    else:
                                        temp.extend(protect)
                                else:
                                    temp.extend(gates_glitch[el])
                            else:
                                temp.append(el)
                    if(Notraceback):
                        self.gadget.reg[sympy_gate]=temp
                    
                    if(self.flag==1):
                        for e in temp:
                            glitch.append({e:float(pr)}) 
                    elif(self.flag==2):
                        for e in temp:
                            if(isinstance(e,Symbol) or isinstance(e,Expr)):
                                glitch.append({e:random()})
                            else:
                                for ee in e:
                                    glitch.append({ee:random()})
                    elif(self.flag==3):
                        for e in temp:
                            
                            if(isinstance(e,Symbol) or isinstance(e,Expr)):
                                glitch.append({e:float(self.gadget.probability)})
                            else:
                                for ee in e:
                                    glitch.append({ee:float(self.gadget.probability)})
                elif(noGlitch==True):
                    for el in postorder_traversal(sympy_logic):
                        if(isinstance(el,Symbol) and el in gates):
                            sympy_logic=sympy_logic.xreplace({el:gates[el]})
                    if(self.flag==1):
                        glitch.append({sympy_logic:float(pr)})
                    elif(self.flag==2):
                        glitch.append({sympy_logic:random()})
                    elif(self.flag==3):
                        glitch.append({sympy_logic:float(self.gadget.probability)})
                    if(sympy_gate in gates):
                        self.gadget.reg[sympy_gate]=gates[sympy_gate]
                    else:
                        self.gadget.reg[sympy_gate]=sympy_logic
                gates[sympy_gate]=sympy_logic  
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic 
                    gates_glitch[sympy_gate]=[]
                    continue
                elif(self.inputs and sympy_gate==sympy_logic and sympy_gate in self.inputs):
                    self.inputs.remove(sympy_gate)
            observation=[]
            observation.extend([*glitch])
            if(not observation and not (sympy_logic.atoms()-sympy_logic.free_symbols)):
                raise RuntimeError("Whoops no observation?")
            self.gadget.mapRow2Obs[rowOfob]=observation
            gates_glitch[sympy_gate] = [key for d in observation for key in d.keys()]
            if(sympy_gate in self.sharesOut):
                ObsOut.update({sympy_gate:rowOfob})
                continue
            ObsIn.append(rowOfob)
        sharesIn_notrans=self.encoding_shares if self.model_str=="probing" and Trans else []
        for item in sharesIn_notrans:
            ObsIn.remove(item)
        return self.gen_allObs(ObsIn,ObsOut,Trans,sharesIn_notrans)

    def gadgetObs_pr(self):
        """
        standard
        """
        if(self.flag==2):
            from random import random
        # --------------------------------------------------------------------------------------
        gates={}
        ObsIn=[]
        ObsOut={}
        # robust 
        if(self.robust>0):
            self.robust_pr_transtional()
            return True
        checkBar = alive_it(self.gadget.expressions) if self.gadget.probaLoop==1 else self.gadget.expressions
        for ob in checkBar:
            try:
                gate,logic=ob.split("=")
            except:
                raise RuntimeError("Incorrect expression in ROW: ",self.gadget.mapRow2exp.inverse[ob])
            if(gate=="reg"):   
                self.gadget.reg[logic]=gate
                continue
            if("[" in logic and "]" in logic):  
                logic=logic[1:-1]
            # evaluate observation
            rowOfob=self.gadget.mapRow2exp.inverse[ob]   
            if(self.model_str!="probing" and rowOfob in self.encoding_shares):    
                continue
            sympy_gate=symbols(gate)

            observation=[]
            if(";" in logic):
                logic,temp=logic.split(";")
                if(self.flag==1):
                    for e in temp.split(","):
                        e,pr=e.split("<")
                        observation.append({sympify(e,convert_xor=False):float(pr)})
                elif(self.flag==2):
                    for e in temp.split(","):
                        observation.append({sympify(e,convert_xor=False):random()})
                elif(self.flag==3):
                    prob=self.gadget.probability
                    for e in temp.split(","):
                        observation.append({sympify(e,convert_xor=False):float(prob)})

            if(logic):
                if(self.flag==1):
                    logic,pr=logic.split("<")
                sympy_logic=sympify(logic,convert_xor=False)
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic 
                    continue
                for el in postorder_traversal(sympy_logic):
                    if(isinstance(el,Symbol) and el in gates):
                        sympy_logic=sympy_logic.xreplace({el:gates[el]})
                gates.update({sympy_gate:sympy_logic}) 
                if(isinstance(sympy_logic,Integer)):
                    gates[sympy_gate]=sympy_logic  
                    continue
                elif(self.inputs and sympy_gate==sympy_logic and sympy_gate in self.inputs):
                    self.inputs.remove(sympy_gate)
            if(self.flag==1):
                observation.append({sympy_logic:float(pr)})
            elif(self.flag==2):
                observation.append({sympy_logic:random()})
            elif(self.flag==3):
                observation.append({sympy_logic:float(self.gadget.probability)})
            if(not observation):
                raise RuntimeError("Whoops no observation?")
            rowOfob=self.gadget.mapRow2exp.inverse[ob]   
            self.gadget.mapRow2Obs[rowOfob]=observation
            if(sympy_gate in self.sharesOut):    
                ObsOut.update({sympy_gate:rowOfob})
                continue
            ObsIn.append(rowOfob)
        
        return self.gen_allObs(ObsIn,ObsOut,False,[])


    def analysis(self):
        
        # --------------------------------------------------------------------------------------
        return self.gadgetInfo()



