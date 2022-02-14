# -*- coding: utf-8 -*-
# Revision of 14 Feb 2022
# The following lines are to enable deletion of a line in a windows command prompt
import sys
from sys import platform
if platform == "win32":
    import ctypes
    kernel32 = ctypes.windll.kernel32
    kernel32.SetConsoleMode(kernel32.GetStdHandle(-11), 7)
#############
# Glossary: #
#############################################################################################
# Expression                                                                                #
#   a string of correctly bracketed characters, including the empty string                  #
# Statement                                                                                 #
#   an non-empty expression of the form [e1][e2][e3]..., where each en is an expression     #
# Atomic statement                                                                          #
#   a statement of the from [e], where e is an expression                                   #
# Substatement of a Statement                                                               #
#   a statement [e1][e2][e3]... is a substatement of a statement [d1][d2][d3]...            #
#   when each en is one of the dm's                                                         #
# Constant                                                                                  #
#   a string of non-bracket characters, including the empty string                          #
# Formula                                                                                   #
#   an expression that is not a statement, which will then have the form c1s1c2s2...        #
#   where c1,c2,... are constants and s2,s2,... are statements, where if there is at        #
#   least one statement then at least one constant must be non-empty                        #
# Variable                                                                                  #
#   a statement [c] where c is a non-empty constant                                         #
# Argument                                                                                  #
#   a formula of the form s1:s2:s3:...:sn where each sn is a statement                      #
# Equation                                                                                  #
#   a formula of the form a1=a2 where a1 and a2 are atomic statements                       #
#                                                                                           #
#############################################################################################                                                                                           #

########################################################################################### 
# THE MAIN MODULE (proposition class)                                                     #
# An object of this class enables the user to build a theorem or an axiom.                #
# This is done by adding individual lines of the proof in the SOFiA language.             #
# The proposition is formalized once the proof has been completed.                        #
# Each line of the proof is added by an instruction referring to valid deduction rules.   #
# If there were mistakes made in the proof, the output will list those.                   #
###########################################################################################
def help():
    print(' ================')
    print(' SOFiA (ver 01080221)')
    print(' ================')
    print(' General commands.')
    print('  ■ Create new proposition: P=sofia.prop("Prop") will create a proposition named "Prop".')
    print('  ■ Postulate: P.p("[X]") will turn a proposition into an axiom stating [X].')
    print('  ■ Show: P.show() will print proposition P on the screen.')
    print('  ■ Show history: P.showh() will print proposition building history for P.')
    print('  ■ Axiom builders: A=sofia.nat() and A=sofia.bool() define axioms builders. Call A.help() to see how to use them.')
    print(' ================')
    print(' Proof building commands. For a given proposition P, the following proof building commands are available.')
    print('  ■ Assumption: P.a("[X]") will assume [X].')
    print('  ■ Restate: P.r([[1,1],[2,3]],["x"]) will combine the statements from line 1, position 1, and from line 2, position 3, in a single line. It will in addition rename the first free variable in each of these statements to "x".')
    print('  ■ Recall: P.c(Prop) will recall a proposition (axiom/theorem) stored as Prop.')
    print('  ■ Selfequate: P.e(2,1) will self-equate the statement at line 2, position 1.')
    print('  ■ Synapsis: P.s() will step out from an assumption block.')
    print('  ■ Apply: P.d(2,[[1,1],[1,2]],3) will apply an implication at line 2, position 3, to variables at line 1, position 1, and line 1, position 2.')
    print('  ■ Left substitution: P.ls(1,2,[3,4],5,6) will substitute the left side of equality at line 1, position 5, in line 2, position 6, replacing occurences 3 and 4 of the right side of the equality.')
    print('  ■ Right substitution: P.rs(1,2,[],5,6) will substitute the right side of equality at line 1, position 5, in line 2, position 6, replacing all occurences of the left side of the equality.')
    print('  ■ Delete: P.x() will delete the last line of the proof.')

class prop:
                    #############################################################
    _al='╔'         # Symbols for the bracket proof display                     #
    _il='║'         #                                                           #            
    _cl='╚'         #                                                           #
    _sal='■'        #    <-This is used to mark a single-line assumption block  #
                    ############################################################# 
    _im=':'         # Symbols for implication, left and right bracket    #
    _lb='['         #    Note: they must be distinct single characters  #
    _rb=']'         #########################################################################
    _sp='$'         # A researved meaningless symbol                                        #
    _eq='='         # Symbol for equality                                                   #                                          
    _pr="'"         # Prime - variable suffix                                               #
    _pm=3           # Upper bound for number of primes automatically appended to a variable #
    _ss=""          # Subscript symbol                                                      #
    _f="!"          # False constant
    _v='?'          # Symbol for disjunction    #
    _ep='QED'           # End proof symbol          #
                        #############################
    def __init__(self,name='Proposition',options=[]):
                                    #############################################################################################
        self._scoped=False          # This detemines the way variables are treated:                                             #                       
        if 'scoped' in options:     # scoped = False means that variables are not limited by the formula scope (default opt.)   #
            self._scoped=True       # scoped = True means that variables are limited by the formula scope (not impl. yet)       #
                                    #############################################################################################        
        self._prfnam='Proof'        # Name of the proof and the proposition, can be changed #
        self._nam=name              #########################################################
        self._proptype='Theorem'

        # The main proof data:
        self._lin=[]     # the sequence of proof lines
        self._rea=[]     # the sequence of explanations how each proof line was obtained
        self._assdep=[]  # the sequence of assumption depths for each proof line
        self._curlin=0   # the index of current line in a proof under construction (subtract one to input in the arrays above)

        # Error texts
        self._err1=' - inval. expr. at L'
        self._err2=' - inval. stat. at L'
        self._err3=' - inval. line ref. at L'
        self._err4=' - no input for synapsis at L'
        self._err5=' - illigal step for the first line of proof at L'
        self._err6=' - proof interrupted at line L'
        self._err7=' - ref. line is not logically accessible at L'
        self._err8=' - inval. final line'
        self._err9=' - inval. initial line'
        self._err10=' - inval. inference at L'
        self._err11=' - inval. concretization at L'
        self._err12=' - concrization with noncontextual variable at L'
        self._err13=' - cannot equate coupound statement at L'
        self._err14=' - there is reserved meaning for notation at L'
        self._err15=' - variables lost in notation at L'
        self._err16=' - invalid notation introduced at L'
        self._err17=' - unrecognized equality referenced at L'
        self._err18=' - you can only recall a sofia proposition at L'
        self._err19=' - generalization failed or partially succeeded at L'
        self._err20=' - disjunction unconfirmed at L'
        self._err21=' - inval. position ref. at L'
        self._err22=' - cannot contextualize reserved variable at L'
        self._err23=' - cannot reserve a context variable at L'
        self._err24=' - void proposition recalled at L'

        # Auxiliary proof data
        self._err=[]     # List of errors in the proof (shown when the proof gets printed)
        self._propsta=''           # Proposition statement 

    def show(self,onlyreturn=False):
        if onlyreturn==False:
            self.QED()
        else:
            return self.QED()

    def showh(self,onlyreturn=False):
        if onlyreturn==False:
            for h in self._err:
                print(h)
        else:
            return self._err

    def getstatement(self):
        if self._proptype=='Axiom':
            print('')
            print('Axiom: '+self._nam+'.')
            print(self._propsta)
            return self._propsta
        elif len(self.QED())>0:
            return self._propsta
        else:
            return self._lb+self._rb
    def t(self,name='Proposition'):
        self._proptype='Theorem'
        self._propsta=self._lb+self._rb
    def p(self,line=''):
        self._err.append('Postulated '+line)
        A=self.postulate(line)
    def postulate(self,line=''):
        success=True
        self._proptype='Axiom'
        if line=='':
            line=self._lb+self._rb

        # Check if the line is a valid expression and a valid statement
        if self._valexp(line)==False:
            line=self._lb+self._rb
            success=False
            self._err.append(self._err1+str(self._curlin))
        elif self._valsta(line)==False:
            line=self._lb+self._rb
            success=False
            self._err.append(self._err2+str(self._curlin)) 
        
        self._propsta=line
        self.show()          
        return line
    def x(self):
        if self._curlin>0:
            self._err.append('Deleted last line')
            self._assdep.pop()
            self._lin.pop()
            self._rea.pop()
            self._curlin=self._curlin-1
            self.show()
        else:
            print('Cannot delete a line in the empty proof')
    ####### Deduction step: ASSUME ##################################################
    # An assumption can be any statement whatsoever.                                #
    # If a reserved variable is stated in the assumption, it will be renamed.       #                       
    #################################################################################
    def a(self,assumption=''):
        if self._proptype=='Theorem':            
            self._err.append('Assumed: '+assumption)
            A=self.assume(assumption)
            self.show()
        else:
            print('Cannot prove an axiom.')
    def assume(self,assumption=''):
        if assumption=='':
            assumption=self._lb+self._rb

        # Determine assumption depth of the new line (increment by one)
        if self._curlin==0:
            self._assdep.append(1)
        else:
            self._assdep.append(self._assdep[self._curlin-1]+1)
        
        self._rea.append('assumption')

        # Update current line index
        self._curlin=self._curlin+1

        # Check if the assumption is a valid expression and a valid statement
        if self._valexp(assumption)==False:
            assumption=self._lb+self._rb
            self._err.append(self._err1+str(self._curlin))        
        elif self._valsta(assumption)==False:
            assumption=self._lb+self._rb
            self._err.append(self._err2+str(self._curlin)) 
        # Add line to the proof
        self._lin.append(self._revisestat(self._cont(self._curlin-1),self._noncont(self._curlin-1),assumption))

        #ascont=self._statcontext(assumption)
        #alldepvar=self._noncont(self._curlin-1)
        #illvars=''
        #if len(ascont)>0:
        #    for r in range(0,len(ascont)):
        #        if ascont[r] in alldepvar:
        #            illvars=illvars+ascont[r]
        #if illvars!='':
        #    if len(ascont)>1:
        #        self._err.append(self._err22+str(self._curlin)+' (variables '+illvars+')')
        #    else:
        #        self._err.append(self._err22+str(self._curlin)+' (variable '+illvars+')')

        # Return new line index
        return self._curlin
    ####### Deduction step: REST #################################################################
    # An upgrade of RESTATE allowing combination of multiple statements                             #
    #   -lineno: line where the the statement to be restated lies.                                  #
    #   -ref: position of the statement to be restated on the given line.                           #
    #   -newvars: new variables to be used as a replacement of noncontextual reserved variables.    #
    #################################################################################################
    def r(self,instance=[],newvars=[]):
        if self._proptype=='Theorem': 
            self._err.append('Restatement: '+str([instance,newvars]))
            A=self.rest(instance,newvars)
            self.show()
        else:
            print('Cannot prove an axiom.')
    def rest(self,instance=[],newvars=[]):
        # The following makes lineno argument optional - default value being current line
        new=''
        reason=''
        alert=''
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])
        for e in instance:
            if len(e)==2:
                lineno=e[0]
                ref=e[1]
                if lineno==-1:
                    lineno=self._curlin
                if self._curlin==0:
                    self._err.append(self._err5+str(self._curlin+1))
                elif lineno<0 or lineno>len(self._lin):
                    self._err.append(self._err3+str(self._curlin+1))
                elif lineno!=0 and self._logdep(lineno-1,self._curlin-1)==False:
                    self._err.append(self._err7+str(self._curlin+1))    
                else:
                    if lineno!=0:
                        reason=reason+' '+str(lineno)    # Add reasoning for the line
                    if lineno>self._curlin or lineno==0:
                        new=new+''
                    else:
                        s=self._extractstat(self._lin[lineno-1])
                        if ref<len(s)+1 and ref>0:
                            newline=s[ref-1]
                        elif ref!=-1:
                            ref=-1
                            new=new+''                
                        else:
                            newline=self._lin[lineno-1]
                        if newvars!=[]:
                            nlcontvars=self._statcontext(newline)
                            contextvars=self._cont(self._curlin)
                            nlvars=self._vars(newline)
                            noncontnewvars=[]
                            for x in newvars:
                                if x not in contextvars and x not in nlvars:
                                    noncontnewvars.append(x)
                            if len(noncontnewvars)!=len(newvars):
                                self._err.append(self._err23+str(self._curlin+1))
                            nlreplvars=[]
                            for i in range(0,len(nlvars)):
                                if nlvars[i] not in contextvars and nlvars[i] not in nlcontvars:
                                    nlreplvars.append(nlvars[i])
                            for i in range(0,len(nlreplvars)):
                                if i<len(newvars):
                                    newline=newline.replace(self._lb+nlreplvars[i]+self._rb,self._lb+newvars[i]+self._rb)
                                else:
                                    i=len(nlreplvars)
                        new=new+newline                    
        # Set assumption depth of the new line   
        if reason=='':
            self._rea.append('restatement (void)')
            new=self._lb+self._rb
        else:
            self._rea.append('restatement (see lines'+reason+')')    # Add reasoning for the line
        if new=='':
            new=elf._lb+self._rb
        self._lin.append(new)
        self._curlin=self._curlin+1
        # Return new line index
        return self._curlin    
    ####### Deduction step: RESTATE #################################################################
    # With this deduction step a previously stated statement can be restated.                       #
    #   -lineno: line where the the statement to be restated lies.                                  #
    #   -ref: position of the statement to be restated on the given line.                           #
    #   -newvars: new variables to be used as a replacement of noncontextual reserved variables.    #
    #################################################################################################
    def restate(self,lineno=-1,ref=-1,newvars=[]):
        # The following makes lineno argument optional - default value being current line
        
        if lineno==-1:
            lineno=self._curlin
        
        if lineno!=0:
            self._rea.append('restatement (see L'+str(lineno)+')')    # Add reasoning for the line
        else:
            self._rea.append('empty formula stated')
        # Check if the line reference is valid and return errors if not
        if self._curlin==0:
            self._err.append(self._err5+str(self._curlin+1))
        elif lineno<0 or lineno>len(self._lin):
            self._err.append(self._err3+str(self._curlin+1))
        elif lineno!=0 and self._logdep(lineno-1,self._curlin-1)==False:
            self._err.append(self._err7+str(self._curlin+1))    

        # Set assumption depth of the new line   
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])

        # Update current line index
        self._curlin=self._curlin+1     

        # Add a line to the proof
        if lineno>self._curlin-1 or lineno==0:
            self._lin.append(self._lb+self._rb)
        else:
            s=self._extractstat(self._lin[lineno-1])
            if ref<len(s)+1 and ref>0:
                newline=s[ref-1]
            elif ref!=-1:
                ref=-1
                self._err.append(self._err21+str(self._curlin))                
            else:
                newline=self._lin[lineno-1]
            if newvars!=[]:
                nlcontvars=self._statcontext(newline)
                contextvars=self._cont(self._curlin-1)
                nlvars=self._vars(newline)
                noncontnewvars=[]
                for x in newvars:
                    if x not in contextvars and x not in nlvars:
                        noncontnewvars.append(x)
                if len(noncontnewvars)!=len(newvars):
                    self._err.append(self._err23+str(self._curlin))
                nlreplvars=[]
                for i in range(0,len(nlvars)):
                    if nlvars[i] not in contextvars and nlvars[i] not in nlcontvars:
                        nlreplvars.append(nlvars[i])
                for i in range(0,len(nlreplvars)):
                    if i<len(newvars):
                        newline=newline.replace(self._lb+nlreplvars[i]+self._rb,self._lb+newvars[i]+self._rb)
                    else:
                        i=len(nlreplvars)
            self._lin.append(newline)
        # Return new line index
        return self._curlin
    ####### Deduction step: RECALL ##################################################
    # This is the deduction step of recalling existing axioms or proved theorems.   #
    #################################################################################
    def c(self,pro=''):
        if self._proptype=='Theorem': 
            if type(pro)==prop:
                self._err.append('Recalled '+pro._nam+': '+pro._propsta)
            else:
                self._err.append('Recalled '+pro)
            A=self.recall(pro)
            self.show()
        else:
            print('Cannot prove an axiom.')

    def recall(self,pro=''):
        # Set assumption depth of the new line   
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])

        # Add a line to the proof
        if type(pro)==prop:
            self._rea.append('recalling '+pro._nam)    # Add reasoning for the line 
            self._lin.append(self._revisestat([],self._noncont(self._curlin),self._resolve([self._statfromformulas(self._cont(self._curlin)),pro.getstatement()],[])[1]))
        else:
            self._rea.append('recall (void)') 
            self._lin.append(self._lb+self._rb)
            self._err.append(self._err18+str(self._curlin+1))

        # Update current line index
        self._curlin=self._curlin+1     

        # Return new line index
        return self._curlin
    ####### Deduction step: SELFEQUATE #######################################
    # In this deduction step a line is equated to itself.                    #
    #   - lineno and ref: position of the statement to be equated to itself  #
    ##########################################################################
    def e(self,lineno=-1,ref=-1):
        if self._proptype=='Theorem': 
            self._err.append('Selfequate '+str([lineno,ref]))
            A=self.selfequate(lineno,ref)
            self.show()
        else:
            print('Cannot prove an axiom.')
    def selfequate(self,lineno=-1,ref=-1):
        # The following makes lineno argument optional - default value being current line
        if lineno==-1:
            lineno=self._curlin    

        # Set assumption depth of the new line   
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])

        # Update current line index
        self._curlin=self._curlin+1     

        if lineno<1 or lineno>len(self._lin):
            self._lin.append(self._lb+self._lb+self._rb+self._eq+self._lb+self._rb+self._rb)
            self._rea.append('self-equate (void)')    # Add reasoning for the line
            self._err.append(self._err3+str(self._curlin))
        elif self._logdep(lineno-1,self._curlin-2)==False:
            self._lin.append(self._lb+self._lb+self._rb+self._eq+self._lb+self._rb+self._rb)
            self._rea.append('self-equate (void)')    # Add reasoning for the line
            self._err.append(self._err7+str(self._curlin))
        else:
            # Check if the line reference is valid and return errors if not
            if ref==-1:
                ref=1
            # Add a line to the proof
            if lineno>self._curlin-1 or lineno<1:
                self._lin.append(self._lb+self._lb+self._rb+self._eq+self._lb+self._rb+self._rb)
                self._rea.append('self-equate (void)')    # Add reasoning for the line
                self._err.append(self._err3+str(self._curlin))
            else:
                s=self._extractstat(self._lin[lineno-1])
                if ref<len(s)+1 and 0<ref:
                    self._rea.append('self-equate from L'+str(lineno)+'('+str(ref)+')')    # Add reasoning for the line
                    self._lin.append(self._lb+s[ref-1]+self._eq+s[ref-1]+self._rb)
                else:
                    self._err.append(self._err21+str(self._curlin))
                    self._rea.append('self-equate (void)')
                    self._lin.append(self._lb+self._lb+self._rb+self._eq+self._lb+self._rb+self._rb)
        # Return new line index
        return self._curlin    
    ####### Deduction step: SYNAPSIS ############################################################
    # This is the deduction step of 'stepping out' from an assumption block.                    #
    # It summarizes the assumption block as an inference of its first and last lines.           #
    # Note that one can only step out of the assumption block when on its last line.            #   
    # Because of this, no line reference is needed for this function.                           #
    # During synapsis, block-specific context variables will be appended to the inference.      #
    # This only happens when the block-specific context variable appears inside the last line.  #  
    #############################################################################################
    def s(self):
        if self._proptype=='Theorem': 
            self._err.append('Synapsis')
            A=self.synapsis()
            self.show()
        else:
            print('Cannot prove an axiom.')

    def synapsis(self):
        if len(self._assdep)==0:
            self._assdep.append(0)
            self._err.append(self._err4+str(self._curlin+1))
            self._lin.append(self._lb+self._lb+self._rb+self._im+self._lb+self._rb+self._rb)
            self._rea.append('synapsis (void)')
            self._curlin=self._curlin+1
        elif self._assdep[self._curlin-1]==0:
            self._assdep.append(0)
            self._err.append(self._err4+str(self._curlin+1))         
            self._lin.append(self._lb+self._lb+self._rb+self._im+self._lb+self._rb+self._rb)
            self._rea.append('synapsis (void)')
            self._curlin=self._curlin+1
        else:
            self._assdep.append(self._assdep[self._curlin-1]-1)
            # Determine the starting line of the assumption block
            i=self._curlin-1
            while self._assdep[i]>self._assdep[self._curlin-1]-1 and i>0:
                i=i-1
            if i==0 and self._assdep[0]>self._assdep[self._curlin-1]-1:
                i=i-1
            lineno=i+1
            if lineno<1:
                blockcont=self._cont(self._curlin-1,0)
            else:
                blockcont=self._cont(self._curlin-1,lineno-1)
            outblockcontext=self._cont(lineno)
            context=self._cont(self._curlin-1)
            asscontext=self._statcontext(self._lin[lineno])
            # Add reasoning for the line
            self._rea.append('synapsis (L'+str(lineno+1)+'-'+str(self._curlin)+')')

            # Update current line index
            self._curlin=self._curlin+1

            # Add the proof line
            if self._curlin>1:
                conclusion=self._lin[self._curlin-2]
                conclusionvars=self._vars(conclusion)
                conclusioncontext=self._statcontext(conclusion)
                addedvars=[]
                for x in conclusionvars:
                    if x in blockcont and x not in outblockcontext and x not in conclusioncontext and x not in asscontext and x not in addedvars:
                        addedvars.append(x)
                        conclusion=self._lb+x+self._rb+conclusion
                if self._scoped==True:
                    newstats=self._resolve([self._lin[lineno],conclusion],context)
                    self._lin.append(self._lb+newstats[0]+self._im+newstats[1]+self._rb)
                else:
                    self._lin.append(self._lb+self._lin[lineno]+self._im+conclusion+self._rb)                
            else:
                self._lin.append(self._lb+self._lb+self._rb+self._im+self._lb+self._rb+self._rb)

        # Return new line index
        return self._curlin
   
    ####### Deduction step: APPLY ###############################################                       
    # Applies a sofia implication if it can be applied.                         #
    #   -lineno: the line from which to retrieve the implication to be applied  #
    #   -linerefs: indicates substitution to be made during implication         #
    #   -ref: position of the formula in the given line                         #
    ############################################################################# 
    def d(self,lineno=-1,linerefs=[],ref=-1):
        if self._proptype=='Theorem': 
            self._err.append('Application: '+str([lineno,linerefs,ref]))
            A=self.apply(lineno,linerefs,ref)
            self.show()
        else:
            print('Cannot prove an axiom.')
    def apply(self,lineno=-1,linerefs=[],ref=-1):
        if lineno==-1:
            lineno=self._curlin
        if ref==-1:
            ref=1
        majorerror=False
        # Check if the line is logically accessible (provided line reference is correct)
        if self._curlin==0:
            majorerror=True
            self._err.append(self._err5+str(self._curlin+1))
        elif self._logdep(lineno-1,self._curlin-1)==False:
            majorerror=True
            self._err.append(self._err7+str(self._curlin+1))                                   
        # Determine assumption depth of the new line (same as previous line)   
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])
        # Check if concretizing variables belong to the context
        contextvars=self._cont(self._curlin)
        allvars=self._noncont(self._curlin)
        linerefstats=[]
        for i in range(0,len(linerefs)):
            if type(linerefs[i])==list:
                if len(linerefs[i])==2:
                    if type(linerefs[i][0])==int and type(linerefs[i][1])==int:
                        if linerefs[i][0] in range(1,len(self._lin)+1):
                            if self._logdep(linerefs[i][0]-1,self._curlin-1):
                                e=self._extractstat(self._lin[linerefs[i][0]-1])
                                if linerefs[i][1] in range(1,len(e)+1):
                                    linerefstats.append(e[linerefs[i][1]-1])
                                else:
                                    self._err.append(self._err21+str(self._curlin+1))
                            else:
                                self._err.append(self._err7+str(self._curlin+1))
                        else:
                            self._err.append(self._err3+str(self._curlin+1))
                    else:
                        self._err.append(self._err7+str(self._curlin+1))
                elif linerefs[i]==[]:
                    linerefstats.append(self._sp)
                else: 
                    self._err.append(self._err7+str(self._curlin+1))
            elif type(linerefs[i])==int:
                if linerefs[i] in range(1,len(self._lin)+1):
                    if self._logdep(linerefs[i]-1,self._curlin-1):
                        e=self._extractstat(self._lin[linerefs[i]-1])
                        linerefstats.append(e[0])
                    else:
                        self._err.append(self._err7+str(self._curlin+1))
                else:
                    self._err.append(self._err3+str(self._curlin+1))                
            else:
                self._err.append(self._err3+str(self._curlin+1))
        # Update current line index
        self._curlin=self._curlin+1        
        # Check if line reference is correct and accordingly, add a line to the proof
        if lineno>self._curlin-1 or lineno<1:
            self._err.append(self._err3+str(self._curlin))
            majorerror=True
        else:
            w=self._extractstat(self._lin[lineno-1])
            if ref>len(w):
                self._err.append(self._err21+str(self._curlin+1))
                ref=1
            l=w[ref-1]
            constants=self._decomposestat(l)[0]
            statements=self._decomposestat(l)[1]
            if constants!=['',self._im]:
                self._err.append(self._err11+str(self._curlin))
                majorerror=True
            else:
                #statements=self._resolve(statements,self._statcontext(statements[0])+contextvars)
                l=self._lb+statements[0]+self._im+statements[1]+self._rb
                assumptionstats=self._extractstat(statements[0])
                abstractvarlist=[]
                for i in range(0,len(assumptionstats)):
                    v=self._vars(assumptionstats[i])
                    if len(v)==1:
                        if self._isvar(assumptionstats[i]) and (v[0] not in abstractvarlist) and (v[0] not in contextvars):
                            abstractvarlist.append(v[0])
                if len(abstractvarlist)>0:
                    if len(linerefstats)>0:
                        for j in range(0,len(abstractvarlist)):
                            if len(linerefstats)<j+1:
                                k=len(linerefstats)-1
                            else:
                                k=j
                            if linerefstats[k]!=self._sp:
                                l=l.replace(self._lb+abstractvarlist[j]+self._rb,linerefstats[k]) 
                possib=False
                pos=[]
                inferfrom=self._extractargstat(l)
                if len(inferfrom)>1:
                    if inferfrom[0]=='':
                        possib=True
                    else:
                        stats=self._extractstat(inferfrom[0])
                        possib=True
                        j=0
                        while j in range(0,len(stats)) and possib==True:
                            found=False
                            i=0
                            while i in range(0,self._curlin) and found==False:
                                if i<len(self._lin) and j<len(stats):
                                    if stats[j] in self._extractstat(self._lin[i]) and self._logdep(i,self._curlin-1):
                                        pos.append(i+1)
                                        found=True
                                i=i+1
                            if found==False:
                                possib=False
                            j=j+1        
                if possib:
                    r=self._revisestat(self._cont(self._curlin-1),self._noncont(self._curlin-1),inferfrom[len(inferfrom)-1])
                    self._lin.append(r)
                else:
                    majorerror=True
                    self._err.append(self._err10+str(self._curlin))
        # Add reasoning for the line
        substitution=''
        if len(linerefstats)>0:
            substitution=linerefstats[0]
            for i in range(1,len(linerefstats)):
                substitution=substitution+','+linerefstats[i]
        if substitution!='':
            substitution=' (with concretization '+substitution+')'
        if majorerror:
            self._rea.append('application (void)')
            self._lin.append(self._lb+self._rb)
        else:
            self._rea.append('application of L'+str(lineno)+'.'+str(ref)+substitution)
        # Return new line index
        return self._curlin   

    ####### Deduction steps: LSUB and RSUB ##############################################################
    # In these deduction steps, a line of the proof gets substituted into according to an equality.     #
    #   -eqline and eqlinref: coordinates of the statement contains the equation to be applied.                                    #
    #   -linen and linref: coordinates of the statement which the substitution needs to take place.                                #
    #   -instanct: the list of positions where the substitution should take place.                      #
    ##################################################################################################### 
    def ls(self,eqline=-1,lineno=-1,instance=[],eqlinref=-1,linref=-1):
        if self._proptype=='Theorem': 
            self._err.append('Left substitution: '+str([eqline,lineno,instance,eqlinref,linref]))
            A=self.lsub(eqline,lineno,instance,eqlinref,linref)
            self.show()
        else:
            print('Cannot prove an axiom.')
    def lsub(self,eqline=-1,lineno=-1,instance=[],eqlinref=-1,linref=-1):
        if eqline==-1:
            eqline=self._curlin
        if lineno==-1:
            lineno=self._curlin-1
        if eqlinref==-1:
            eqlinref=1
        if linref==-1:
            linref=1
        noequality=False
        line=self._lb+self._rb
        eqLHS=''
        eqRHS=''

        if eqline>0 and eqline<len(self._lin)+1:
            s=self._extractstat(self._lin[eqline-1])
            if eqlinref<len(s)+1 and 0<eqlinref:
                D=self._decomposestat(s[eqlinref-1])
            else:
                D=[[]]
            if D[0]!=['',self._eq]:
                noequality=True
                self._err.append(self._err17+str(self._curlin+1))
            elif len(D[1])!=2:
                noequality=True
                self._err.append(self._err17+str(self._curlin+1))
            else:
                eqLHS=D[1][0]
                eqRHS=D[1][1]

        else:
            noequality=True
            self._err.append(self._err17+str(self._curlin+1))
        if self._logdep(eqline-1,self._curlin-1)==False:
            noequality=True
            self._err.append(self._err7+str(self._curlin+1))
        
        if self._curlin==0:
            noequality=True
            self._err.append(self._err5+str(self._curlin+1))
        if lineno<1 or lineno>len(self._lin):
            noequality=True
            self._err.append(self._err3+str(self._curlin+1))
        else:
            t=self._extractstat(self._lin[lineno-1])
            if linref<len(t)+1 and 0<linref and noequality==False:
                line=t[linref-1]
            else:
                line=self._lb+self._rb
            if eqline<1 or eqline>len(self._lin):
                noequality=True
                line=self._lb+self._rb
                self._err.append(self._err3+str(self._curlin+1))
        if self._logdep(lineno-1,self._curlin-1)==False:
            noequality=True
            line=self._lb+self._rb
            self._err.append(self._err7+str(self._curlin+1))

        # Determine assumption depth of the new line (same as previous line)   
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])

        if noequality==False:
            res=self._resolve([eqLHS,eqRHS,line],self._cont(self._curlin))
            eqLHS=res[0]
            eqRHS=res[1]
            line=res[2]
            self._rea.append('left substitution, L'+str(eqline)+'('+str(eqlinref)+') in L'+str(lineno)+'('+str(linref)+')') 
            if len(instance)>0:
                k=0
                for n in range(0,len(instance)):
                    line=self._nth_repl(line,eqRHS,eqLHS,instance[n+k])
                    k=k-1
            else:
                line=line.replace(eqRHS,eqLHS)
        else:
            self._rea.append('left substitution (void)')
        
        self._lin.append(line)                

        # Update current line index
        self._curlin=self._curlin+1
        # Return new line index
        return self._curlin
    def rs(self,eqline=-1,lineno=-1,instance=[],eqlinref=-1,linref=-1):
        if self._proptype=='Theorem': 
            self._err.append('Right substitution: '+str([eqline,lineno,instance,eqlinref,linref]))
            A=self.rsub(eqline,lineno,instance,eqlinref,linref)
            self.show()
        else:
            print('Cannot prove an axiom.')
    def rsub(self,eqline=-1,lineno=-1,instance=[],eqlinref=-1,linref=-1):
        if eqline==-1:
            eqline=self._curlin
        if lineno==-1:
            lineno=self._curlin-1
        if eqlinref==-1:
            eqlinref=1
        if linref==-1:
            linref=1
        noequality=False
        line=self._lb+self._rb
        eqLHS=''
        eqRHS=''
        # Add reasoning for the line

        if eqline>0 and eqline<len(self._lin)+1:
            s=self._extractstat(self._lin[eqline-1])
            if eqlinref<len(s)+1 and 0<eqlinref:
                D=self._decomposestat(s[eqlinref-1])
            else:
                D=[[]]
            if D[0]!=['',self._eq]:
                noequality=True
                self._err.append(self._err17+str(self._curlin+1))
            elif len(D[1])!=2:
                noequality=True
                self._err.append(self._err17+str(self._curlin+1))
            else:
                eqLHS=D[1][1]
                eqRHS=D[1][0]
        else:
            noequality=True
            self._err.append(self._err17+str(self._curlin+1))
        if self._logdep(eqline-1,self._curlin-1)==False:
            noequality=True
            self._err.append(self._err7+str(self._curlin+1))
        
        if self._curlin==0:
            noequality=True
            self._err.append(self._err5+str(self._curlin+1))
        if lineno<1 or lineno>len(self._lin):
            noequality=True
            self._err.append(self._err3+str(self._curlin+1))
        else:
            t=self._extractstat(self._lin[lineno-1])
            if linref<len(t)+1 and 0<linref and noequality==False:
                line=t[linref-1]
            else:
                line=self._lb+self._rb
            if eqline<1 or eqline>len(self._lin):
                noequality=True
                line=self._lb+self._rb
                self._err.append(self._err3+str(self._curlin+1))
        if self._logdep(lineno-1,self._curlin-1)==False:
            noequality=True
            line=self._lb+self._rb
            self._err.append(self._err7+str(self._curlin+1))

        # Determine assumption depth of the new line (same as previous line)   
        if self._curlin==0:
            self._assdep.append(0)
        else:
            self._assdep.append(self._assdep[self._curlin-1])
            
        if noequality==False:
            res=self._resolve([eqLHS,eqRHS,line],self._cont(self._curlin))
            eqLHS=res[0]
            eqRHS=res[1]
            line=res[2]
            self._rea.append('right substitution, L'+str(eqline)+'('+str(eqlinref)+') in L'+str(lineno)+'('+str(linref)+')') 
            if len(instance)>0:
                k=0
                for n in range(0,len(instance)):
                    line=self._nth_repl(line,eqRHS,eqLHS,instance[n+k])
                    k=k-1
            else:
                line=line.replace(eqRHS,eqLHS)
        else:
            self._rea.append('right substitution (void)') 
        
        self._lin.append(line)
        # Update current line index
        self._curlin=self._curlin+1
        # Return new line index
        return self._curlin 

    ####### Deduction step: QED ###########################################################################
    # This indicates completion of the proof. The proof is then displayed along with the list of errors   #
    ####################################################################################################### 
    def QED(self):
        p=[] 
        if self._proptype=='Axiom':
            print('')
            p.append('')
            print('Axiom: '+self._nam+'.')
            p.append('Axiom: '+self._nam+'.')
            print(self._propsta)
            p.append(self._propsta)
        elif self._proptype=='Theorem':
            print('')
            p.append('')
            print('Theorem: '+self._nam+'.')
            p.append('Theorem: '+self._nam+'.')
            if self._curlin<1:
                print('Empty theorem.')
                p.append('Empty theorem.')
                return False
            else:
                if self._assdep[self._curlin-1]==0:
                    context=self._cont(self._curlin-1)
                    conclusion=self._lin[self._curlin-1]
                    if self._curlin>1:
                        conclusionvars=self._vars(conclusion)
                        conclusioncontext=self._statcontext(conclusion)
                        addedvars=[]
                        for x in conclusionvars:
                            if x in context and x not in conclusioncontext and x not in addedvars:
                                addedvars.append(x)
                                conclusion=self._lb+x+self._rb+conclusion
                    self._propsta=conclusion
                    print(self._propsta) 
                    p.append(self._propsta)     
                else:
                    self._propsta=self._lb+self._rb
                    print(self._propsta)
                    p.append(self._propsta)
                print(self._prfnam+'.')
                p.append(self._prfnam+'.')
                for i in range(0,len(self._lin)):
                    prefix=''
                    if i==0:
                        if self._assdep[i]==0:
                            prefix=''
                        else:
                            if len(self._assdep)>1:
                                if self._assdep[1]==0:
                                    prefix=self._sal
                                else:
                                    prefix=self._al
                            else:
                                prefix=self._al
                    elif i==len(self._lin)-1:
                        if self._assdep[i]==0:
                            prefix=''
                        elif self._assdep[i-1]<self._assdep[i]:
                            prefix=self._al
                        elif self._assdep[i-1]==self._assdep[i]:
                            prefix=self._il
                        else:
                            prefix=self._cl
                    else:        
                        if self._assdep[i]==0:
                            prefix=''
                        elif self._assdep[i-1]<self._assdep[i] and self._assdep[i+1]>self._assdep[i]-1:
                            prefix=self._al
                        elif self._assdep[i-1]<self._assdep[i] and self._assdep[i+1]<self._assdep[i]:
                            prefix=self._sal
                        elif self._assdep[i-1]==self._assdep[i] and self._assdep[i+1]==self._assdep[i]:
                            prefix=self._il
                        elif self._assdep[i-1]>self._assdep[i]-1 and self._assdep[i+1]<self._assdep[i]:
                            prefix=self._cl
                        elif self._assdep[i-1]>self._assdep[i]-1 and self._assdep[i+1]>self._assdep[i]-1:
                            prefix=self._il
                    for j in range(0,self._assdep[i]-1):
                        prefix=self._il+prefix
                    context='none'
                    if self._scoped==True:                
                        c=self._cont(i)
                    else:
                        c=self._noncont(i)
                    if len(c)>0:
                        context=c[0] 
                    for j in range(1,len(c)):
                        context=context+','+c[j]
                    line=self._displaystat(self._lin[i]) 
                    print(' '+prefix+''+line+' /L'+str(i+1)+': '+self._rea[i]+'.')
                    p.append(' '+prefix+''+line+' /L'+str(i+1)+': '+self._rea[i]+'.')
                print(self._ep)
                p.append(self._ep)
                return p

    def subin(self,form,variables,context):
        formvars=self._vars(form)
        subformvars=[]
        output=form
        for x in formvars:
            if x not in context:
                subformvars.append(x)
        for i in range(0,min(len(subformvars),len(variables))):
            output=output.replace(self._lb+subformvars[i]+self._rb,self._lb+variables[i]+self._rb)
        return self._lb+output+self._rb

    def _revisestat(self,contextvars,reservedvars,statement):
        statcontextvars=self._statcontext(statement)
        statreservedvars=self._vars(statement)
        output=statement
        for x in statcontextvars:
            if x in reservedvars and x not in contextvars:
                output=output.replace(self._lb+x+self._rb, self._lb+self._renamevar(x,reservedvars+statreservedvars)+self._rb)
        return output

    def _nth_repl(self,s, sub, repl, n=-1):
        if n==-1:
            n=1
        find = s.find(sub)
        if find>-1:
            i=1
            while find != -1 and i != n:
                find = s.find(sub, find + 1)
                i = i+1
        
            if i == n and find != -1:
                return s[:find] + repl + s[find+len(sub):]
        return s            

    def _cleanupline(self,line,lineno):
        stats=self._extractstat(line)
        removedstats=[]
        for i in range(0,lineno-1):
            if self._logdep(i,lineno-1):
                compareto=self._extractstat(self._lin[i])
                for x in stats:
                    if x in compareto:
                        removedstats.append(x)
        output=''
        for x in stats:
            if x not in removedstats:
                output=output+x
        if output=='':
            output=self._lb+self._rb
        return output
    # Returns whether the stated formula can be found in an expression with possibly different variable inputs     
    def _instance(self,statform,expression):
        if self._isvar(statform):
            if expression.find(statform)>-1:
                return True
            else:
                return False           
        else:
            f=self._extractformula(statform)
            e=expression
            fvars=self._vars(f)
            evars=self._vars(e)
            for i in range(0,len(fvars)):
                f=f.replace(self._lb+fvars[i]+self._rb,self._lb+self._sb+self._rb)
            for i in range(0,len(evars)):
                e=e.replace(self._lb+evars[i]+self._rb,self._lb+self._sb+self._rb)
            if e.find(self._lb+f+self._rb)>-1:
                return True
            else:
                return False
        
    def _extractformula(self,statement):      # Returns the formula in a single statement
        output=''
        for i in range(1,len(statement)-1):
            output=output+statement[i]
        return output

    def _singlestat(self,statement):     # Returns input if single statement and empty statement otherwise
        output=self._lb+self._rb
        if len(statement)>2:
            if self._valexp(statement) and self._valsta(statement):
                extract=self._extractstat(statement)
                if len(extract)==1:
                    output=statement 
        return output  

    def _statcontext(self,statement):    # Returns list of outer variables in a statement
        output=[]
        e=self._extractstat(statement)
        for x in e:
            if self._isvar(x):
                output.append(self._extractformula(x))
        return output

    def _extractstat(self,statement):    # Extracts outer level statements from an expression
        output=[]
        i=0
        while i in range(0,len(statement)):
            if statement[i]==self._lb:
                s=self._lb
                d=1
                j=i+1
                while j in range(i+1,len(statement)) and d>0:
                    if statement[j]==self._lb:
                        d=d+1
                    elif statement[j]==self._rb:
                        d=d-1
                    s=s+statement[j]
                    j=j+1
                output.append(s)
                i=j
            else:
                i=i+1
        return output
    
    def _displaystat(self,statement):
        #s=self._extractstat(statement)
        #for i in range(0,len(s)):
        #    if self._isvar(s[i]):
        #        s[i]=' given '+self._extractformula(s[i])
        #    else:
        #        yi=self._decomposestat(s[i])
        #        for j in range(0,len(yi[1])):
        #            zij=self._extractstat(yi[1][j])
        #            t=''
        #            for u in zij:
        #                v=self._extractformula(u)
        #                t=t+' '+v+' ' 
        #            yi[1][j]=t
        #        newsi=''
        #        for k in range(0,len(yi[0])):
        #            newsi=newsi+yi[0][k]+yi[1][k]
        #        s[i]=newsi
        #output=s[0]
        #for n in range(1,len(s)):
        #    output=output+', '+s[n]
        return statement
        #s=self._extractstat(statement)
        #output=' '+self._extractformula(s[0])
        #for i in range(1,len(s)):
        #    output=output+'; '+self._extractformula(s[i])
        #output=output.replace(self._eq,' ≡ ')
        #output=output.replace(self._im,' »» ')
        #return output 

    def _extractargstat(self,statement):     # Extracts outer level statements from a stated argument
        output=[]
        stat=''
        i=1
        while i in range(1,len(statement)):
            if statement[i]!=self._im:
                if statement[i]==self._lb:
                    s=self._lb
                    d=1
                    j=i+1
                    while j in range(i+1,len(statement)) and d>0:
                        if statement[j]==self._lb:
                            d=d+1
                        elif statement[j]==self._rb:
                            d=d-1
                        s=s+statement[j]
                        j=j+1
                    stat=stat+s
                    i=j
                else:
                    i=i+1
            elif statement[i]==self._im:
                output.append(stat)
                stat=''
                i=i+1
        output.append(stat)
        return output

    def _decomposestat(self,statement):  # Decompose a stated formula into an array of constants and statements
        states=[]
        constants=[]
        stat=''
        cons=''
        i=1
        while i in range(1,len(statement)):
            if statement[i]==self._lb:
                if i==1 and cons=='':
                    constants.append(cons)
                elif len(cons)>0 and cons!='':
                    constants.append(cons) 
                cons=''
                s=self._lb
                d=1
                j=i+1
                while j in range(i+1,len(statement)) and d>0:
                    if statement[j]==self._lb:
                        d=d+1
                    elif statement[j]==self._rb:
                        d=d-1
                    s=s+statement[j]
                    j=j+1
                stat=stat+s
                i=j
            else:
                if stat!='':
                    states.append(stat)
                if statement[i]!=self._rb:
                    cons=cons+statement[i]
                stat=''
                i=i+1
        if len(constants)==0 and cons=='':
            constants.append(cons)
        elif len(cons)>0 and cons!='':
            constants.append(cons)        
        return [constants,states]
    
    def _resolve(self,statements,context):   # Eliminates variable conflict in an array of statements, based on a context
        output=[statements[0]]
        for i in range(1,len(statements)):
            conclusion=statements[i]
            conclusionvars=self._vars(conclusion)
            premisevars=[]
            for j in range(0,len(output)):
                premisevars=premisevars+self._vars(output[j])
            for x in conclusionvars:
                if x in premisevars and x not in context:
                    renamex=self._renamevar(x,context+conclusionvars+premisevars)
                    conclusion=conclusion.replace(self._lb+x+self._rb,self._lb+renamex+self._rb)
            output.append(conclusion)
        print(output)
        return output
    
    def _renamevar(self,varname,notvars):    # Renames a variable name that does not appear in the list
        newname=varname
        primecount=0
        for i in range(0,len(varname)):
            if varname[i]==self._pr:
                primecount=primecount+1
        i=0
        while newname in notvars:
            if primecount<self._pm and varname[len(varname)-1]!=self._pr:
                newname=newname+self._pr
                primecount=primecount+1
            else:
                newname=newname+self._pr
                newname=varname+self._ss+str(i)
                i=i+1
        return newname
    
    def _cont(self,linenumber,fromline=1):  # Returns the variable context of a line in the proof
        output=[]
        for i in range(fromline-1,linenumber):
            if len(self._vars(self._lin[i]))>0:
                if self._logdep(i,linenumber)==True:
                    s=self._extractstat(self._lin[i])
                    for v in s:
                        w=self._extractformula(v)
                        if self._isvar(v) and (w not in output):
                            output.append(w)
        return output

    def _statfromformulas(self, formulas):
        output=''
        for i in range(0,len(formulas)):
            output=output+self._lb+formulas[i]+self._rb
        if output=='':
            output=self._lb+self._rb
        return output

    def _noncont(self,linenumber):   # Returns all variables that logically influence a given line in a non-scoped proof
        output=[]
        for i in range(0,linenumber):
            if self._logdep(i,linenumber)==True:
                output=output+self._vars(self._lin[i])
        if len(output)>0:
            output=list(dict.fromkeys(output))
            output.sort()
        return output

    def _isvar(self,statement):               # Checks whether the input is a stated variable
        l=len(statement)
        if l<3:
            return False
        if statement[0]!=self._lb:
            return False
        if statement[l-1]!=self._rb:
            return False
        for i in range(1,l-1):
            if statement[i]==self._lb:
                return False
        return True 
    
    def _vars(self,exp):     # Returns the list of all variables in a given expression
        output=[]
        for i in range(0,len(exp)):
            if exp[i]==self._lb:
                j=i+1
                variable=''
                isvariable=True
                while exp[j]!=self._rb and isvariable==True and j<len(exp):
                    if exp[j]==self._lb:
                        isvariable=False
                    variable=variable+exp[j]
                    j=j+1
                if isvariable==True and variable!='':
                    output.append(variable)
        return output                                          
    
    def _logdep(self,line1,line2):   # Check if lines are in logical dependence
        if line2>-1 and line1>-1 and line1<line2+1:
            i=line1
            while i<line2 and self._assdep[i]>self._assdep[line1]-1:
                i=i+1
            if self._assdep[i]<self._assdep[line1]:
                return False
            return True
        else:
            return False                        

    def _valexp(self,line):
        counter=0
        for i in range(0,len(line)):
            if line[i]==self._lb:
                counter=counter+1
            if line[i]==self._rb:
                counter=counter-1
            if counter<0:
                return False
        if counter!=0:
            return False
        return True
    def _valsta(self,line):
        if self._valexp(line)==False:
            return False          
        counter=0
        for i in range(0,len(line)):
            if line[i]==self._lb:
                counter=counter+1
            elif line[i]==self._rb:
                counter=counter-1
            elif counter==0:
                return False
        if len(line)==0:
            return False
        return True
    def _printline(self,printlineno):
        for i in range(printlineno,printlineno+1):
            prefix=''
            if i==0:
                if self._assdep[i]==0:
                    prefix=''
                else:
                    if len(self._assdep)>1:
                        if self._assdep[1]==0:
                            prefix=self._sal
                        else:
                            prefix=self._al
                    else:
                        prefix=self._al
            elif i==len(self._lin)-1:
                if self._assdep[i]!=1:
                    if self._assdep[i]==0:
                        prefix=''
                    elif self._assdep[i-1]<self._assdep[i]:
                        prefix=self._al
                    elif self._assdep[i-1]==self._assdep[i]:
                        prefix=self._il
                    else:
                        prefix=self._il
                else:
                    prefix=self._il
            else:        
                if self._assdep[i]==0:
                    prefix=''
                elif self._assdep[i-1]<self._assdep[i] and self._assdep[i+1]>self._assdep[i]-1:
                    prefix=self._al
                elif self._assdep[i-1]<self._assdep[i] and self._assdep[i+1]<self._assdep[i]:
                    prefix=self._sal
                elif self._assdep[i-1]==self._assdep[i] and self._assdep[i+1]==self._assdep[i]:
                    prefix=self._il
                elif self._assdep[i-1]>self._assdep[i]-1 and self._assdep[i+1]<self._assdep[i]:
                    prefix=self._il
                elif self._assdep[i-1]>self._assdep[i]-1 and self._assdep[i+1]>self._assdep[i]-1:
                    prefix=self._il
            for j in range(0,self._assdep[i]-1):
                prefix=self._il+prefix
            context='none'
            if self._scoped==True:                
                c=self._cont(i)
            else:
                c=self._noncont(i)
            if len(c)>0:
                context=c[0] 
            for j in range(1,len(c)):
                context=context+','+c[j] 
            line=self._lin[i].replace(self._rb+self._lb, self._rb+' '+self._lb)
            line=line.replace(self._im,' => ')
            print(' '+prefix+''+line+' /L'+str(i+1)+': '+self._rea[i]+'.')

class set:
    _s='set'
    _i='in'
    _t='|'
    def __init__(self,setname='set',el='in'):
        self._s=setname
        self._i=el
    def c(self,stat='',x='x',context=''):
        C=prop("Sets: Restricted Comprehension")
        x=C._lb+x+C._rb
        X='X'
        C._renamevar(X,C._vars(stat+context+x))
        X=C._lb+X+C._rb
        y='y'
        C._renamevar(y,C._vars(stat+context+x))
        y=C._lb+y+C._rb
        s=C._lb+x+self._i+X+self._t+stat+C._rb
        C.postulate(C._lb+context+X+C._lb+X+self._s+C._rb+C._im+C._lb+s+C._lb+s+self._s+C._rb+C._lb+C._lb+y+C._im+C._lb+C._lb+y+self._i+s+C._rb+C._eq+stat.replace(x,y)+C._rb+C._rb+C._rb+C._rb+C._rb)
        print(C._lb+context+X+C._lb+X+self._s+C._rb+C._im+C._lb+s+C._lb+s+self._s+C._rb+C._lb+C._lb+y+C._im+C._lb+C._lb+y+self._i+s+C._rb+C._eq+stat.replace(x,y)+C._rb+C._rb+C._rb+C._rb+C._rb)
        return C
class nat:
    _s='1+'
    _n='nat'
    _z='0'
    _f='!'
    def __init__(self,successor='1+',natnumbertypename='nat',falsename='!'):
        self._s=successor
        self._n=natnumbertypename
        self._f=falsename

    def z(self):
        I=prop("Arithmetic: Zero")
        zerogiven=I._lb+self._z+I._lb+I._rb+I._rb
        zeronumber=I._lb+I._lb+self._z+I._lb+I._rb+I._rb+self._n+I._rb
        zeroissuc=I._lb+I._lb+self._z+I._lb+I._rb+I._rb+I._eq+I._lb+self._s+I._lb+'n'+I._rb+I._rb+I._rb
        zeronotsuccesssor=I._lb+I._lb+'n'+I._rb+I._lb+I._lb+'n'+I._rb+self._n+I._rb+zeroissuc+I._im+I._lb+self._f+I._lb+I._rb+I._rb+I._rb
        I.postulate(zerogiven+zeronumber+zeronotsuccesssor)
        return I

    def s(self):
        I=prop("Arithmetic: Successor")
        nnumber=I._lb+'n'+I._rb+I._lb+I._lb+'n'+I._rb+self._n+I._rb
        sucnumber=I._lb+self._s+I._lb+'n'+I._rb+I._rb+I._lb+I._lb+self._s+I._lb+'n'+I._rb+I._rb+self._n+I._rb
        mnumber=I._lb+'m'+I._rb+I._lb+I._lb+'m'+I._rb+self._n+I._rb
        sucinj=I._lb+mnumber+I._lb+I._lb+self._s+I._lb+'n'+I._rb+I._rb+I._eq+I._lb+self._s+I._lb+'m'+I._rb+I._rb+I._rb+I._im+I._lb+I._lb+'n'+I._rb+I._eq+I._lb+'m'+I._rb+I._rb+I._rb
        I.postulate(I._lb+nnumber+I._im+sucnumber+sucinj+I._rb)
        return I

    def i(self,stat='',context='',var='n'):
        I=prop("Arithmetic: Induction on "+var+" in "+context+stat)
        var=I._lb+var+I._rb
        nextstat=stat.replace(var,I._lb+self._s+var+I._rb)
        z=stat.replace(var,I._lb+self._z+I._lb+I._rb+I._rb)
        i=I._lb+var+I._lb+var+self._n+I._rb+stat+I._im+nextstat+I._rb
        c=I._lb+var+I._lb+var+self._n+I._rb+I._im+stat+I._rb
        I.postulate(I._lb+context+z+i+I._im+c+I._rb)
        return I

    def help(self):
        print(' ================')
        print(' Arithmetic Axiom Builder for SOFiA (ver 1010021)')
        print(' ================')
        print(' Arithmetic axiom building commands. For a given arithmetic axiom builder N, the following axiom building commands are available.')
        print('  ■ Number zero: N.z() will return the axiom (prop object) stating properties of the number zero.')
        print('  ■ Successor: N.s() will return the axiom (prop object) stating properties of the successor function.')
        print('  ■ Induction: N.i("[blabla[n][m][k]]","[m][k]","[n]") will return the axiom (prop object) stating that for all [m][k], the statement [blabla[n][m][k]]] can be proved by induction on [n].')

class bool:
    _em=False
    _f='!'
    _v='?'
    def __init__(self,lawofexcludedmiddle=False,falsesym='!',orsym='?'):
        self._em=lawofexcludedmiddle
        self._f=falsesym
        self._v=orsym

    def f(self,stat='',context=''):
        I=prop("Boolean: False Universality")
        if stat=='':
            stat=I._lb+I._rb
        I.postulate(I._lb+context+I._lb+self._f+I._lb+I._rb+I._rb+I._im+stat+I._rb)
        return I
    def n(self,stat='',context=''):
        I=prop("Boolean: Double Negation")
        if stat=='':
            stat=I._lb+I._rb
        I.postulate(I._lb+context+I._lb+I._lb+stat+I._im+I._lb+self._f+I._lb+I._rb+I._rb+I._rb+I._im+I._lb+self._f+I._lb+I._rb+I._rb+I._rb+I._im+stat+I._rb)
        return I
    def help(self):
        print(' ================')
        print(' Boolean Axiom Builder for SOFiA (ver 1010021)')
        print(' ================')
        print(' Boolean axiom building commands. For a given Boolean axiom builder B, the following axiom building commands are available.')
        print('  ■ False universality: B.f("[blabla[X][Y]]","[X][Y]") will return the axiom "[[X][Y][![]]:[blabla[X][Y]]]" as a prop object.')
        print('  ■ Double negation: B.n("[blabla[X][Y]]","[X][Y]") will return the axiom "[[X][Y][[[blabla[X][Y]]:[![]]]:[![]]]]:[blabla[X][Y]]]".')