
class gadget():
    """ gadget class.
    """
    def __init__(self,name,expressions,mapGates,mapRow2exp,mapRow2Obs,encodingRow,secrets,secretsBits,secretsInputs,secretsInputsBits,secretsOutputs,secretsOutputsBits,invertible,shareNum,shareIndex,randoms,probaLoop,probability,para,bits,field,logic,observationsIn,observationsOutput,observationsCheck,checksize,paraCheck,reg,rpcoeff,obs_mi,checkOptions):
        # basic info
        self.name=name
        self.expressions=expressions
        self.mapGates=mapGates
        self.mapRow2exp=mapRow2exp
        self.mapRow2Obs=mapRow2Obs
        self.encodingRow=encodingRow
        self.secrets=secrets
        self.secretsBits=secretsBits
        self.secretsInputs=secretsInputs
        self.secretsInputsBits=secretsInputsBits
        self.secretsOutputs=secretsOutputs
        self.secretsOutputsBits=secretsOutputsBits
        self.invertible=invertible
        self.shareNum=shareNum
        self.shareIndex=shareIndex
        self.randoms=randoms
        self.probability=probability
        self.probaLoop=probaLoop
        self.para=para
        self.bits=bits
        self.field=field
        self.logic=logic
        

        # Check
        self.observationsIn=observationsIn
        self.observationsOutput=observationsOutput 
        self.observationsCheck=observationsCheck
        self.checksize=checksize
        self.paraCheck=paraCheck
        self.reg=reg
        self.rpcoeff=rpcoeff

        self.obs_mi=obs_mi


        # Check using.
        self.checkOptions=checkOptions          # [detail,mi,write,stop,coefficient,conditions,.robust,model,threshold]
        
    def printParams(self):
        print("Name = %s".rjust(50,"-") %(self.name))
        #print("Expressions = %s".rjust(50,"-") %(self.expressions))
        #print("The number of expressions = %s".rjust(50,"-") %(len(self.expressions)))
        print("Gates = %s".rjust(50,"-") %(self.mapGates))
        print("Secrets = %s".rjust(50,"-") %(str(self.secrets)))
        print("Secrets (bits) = %s".rjust(50,"-") %(str(self.secretsBits)))
        print("Shares's number = %s".rjust(50,"-") %(str(self.shareNum)))
        print("Shares's index = %s".rjust(50,"-") %(str(self.shareIndex)))
        print("Inputs = %s".rjust(50,"-") %(str(self.secretsInputs)))
        print("Inputs (bits) = %s".rjust(50,"-") %(str(self.secretsInputsBits)))
        print("Outputs = %s".rjust(50,"-") %(str(self.secretsOutputs)))
        print("Outputs (bits) = %s".rjust(50,"-") %(str(self.secretsOutputsBits)))
        print("Randoms = %s".rjust(50,"-") %(str(self.randoms)))
        from galois import GF
        print("Field = %s".rjust(50,"-") %(GF(self.field)))
        print("recovery probability mode= %s".rjust(50,"-") %(self.probability))
        if(str(self.probability)=="random"):
            print("loop= %s".rjust(50,"-") %(self.probaLoop))
        #print("Internal Probes = %s".rjust(50,"-") %(self.observationsIn))
        print("Output Probes = %s".rjust(50,"-") %(self.observationsOutput))
        print("All Probes = %s".rjust(50,"-") %(self.mapRow2Obs))
        print("Total checking observations number= \033[1;33m %s \033[0m".rjust(62,"-") %(self.checksize))
        print("Total Internal Probes = %s".rjust(50,"-") %(len(self.mapRow2Obs)-len(self.observationsOutput)))
        print("Total Output Probes = %s".rjust(50,"-") %(len(self.observationsOutput)))
        print("Total Regs (protected gates) = %s".rjust(50,"-") %(len(self.reg)))
        #print("Max coefficient (random probing model) = %d".rjust(50,"-") %(len(self.rpcoeff)))
        print("Check options = %s".rjust(50,"-") %(self.checkOptions))
    
    def saveToFile(self):
        #with open("version18/checkResult/"+self.name+".txt",'a') as file:   # testFile.py
        with open("checkResult/"+self.name+".txt",'a') as file:
            for el in self.obs_mi:
                if(self.obs_mi[el]=="?"):
                    file.writelines(f"{str(el)}:{self.obs_mi[el]}\n")
                elif(self.obs_mi[el]>0):
                    file.writelines(f"{str(el)}:{self.obs_mi[el]}\n")
            from datetime import datetime
            from galois import GF
            file.writelines(f"security:{self.checkOptions['security']},robust:{self.checkOptions['robust']},field:{GF(self.field)} Finished on %s".rjust(200,"-") %(datetime.now().strftime("%Y-%m-%d %H:%M:%S")+"\n"))
        print("result saved. total leakage (%s)" %(len(self.obs_mi)))
    def clearAll(self):
        self.name=""
        self.expressions=[]
        self.mapGates={}
        self.mapRow2exp={}
        self.mapRow2Obs={}
        self.encodingRow=[]
        self.secrets=()
        self.secretsBits=()
        self.secretsInputs=()
        self.secretsInputsBits=()
        self.secretsOutputs=()
        self.secretsOutputsBits=()
        self.invertible=()
        self.shareNum=0
        self.shareIndex={}
        self.randoms=()
        self.probability="f"
        self.probaLoop=1
        self.para=1
        self.bits=1
        self.field=2
        self.logic=True
        
        self.observationsIn=[]
        self.observationsOutput={} 
        self.observationsCheck=[]
        self.checksize=0
        self.paraCheck={}
        self.reg={}
        self.rpcoeff=[]

        self.obs_mi={}

        self.checkOptions={"path":"","security":"","robust":[],"tech.":"","abort":"","detail":"","toFile":"","mcore":1,"maxhours":12,"maxmem":5,"threshold":-1}
