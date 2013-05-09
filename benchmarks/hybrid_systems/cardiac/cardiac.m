% ===============================================================
% ==   Minimal Resistor Model (4 state variables)              ==
% ==                                                           ==
% ==   Supplement for the CMACS Workshop                       ==
% ==                                                           ==
% ==                                                           ==
% ==   Author:                                                 ==
% ==                                                           ==
% ==     E. Bartocci                                           ==
% ==                                                           == 
% ==   Date:  11/05/10                                         ==
% ==                                                           ==
% ==   Free distribution with authors permission               ==
% ==                                                           ==
% ==   SUNY Stony Brook, Stony Brook, NY                       ==
% ==                                                           == 
% ===============================================================  

% The following are the parameters that you can find in the paper 
% A. Bueno-Orovio, M. Cherry, and F. Fenton, ?Minimal model for 
% human ventricular action potentials in tissue,? Journal of 
% Theoretical Biology, no. 253, pp. 544?560, 2008. 


function [out] = single_cell_mrm4V ()

         global EPI_TVP; 
         global EPI_TV1M;  
         global EPI_TV2M; 

         global EPI_TWP;   

         global EPI_TW1M; %190    
         global EPI_TW2M;
         
         global EPI_TS1;
         global EPI_TS2;
         global EPI_TFI;
         global EPI_TO1;
         global EPI_TO2;
         global EPI_TSO1;
         global EPI_TSO2;

         global EPI_TSI;


         global EPI_TWINF;
         global EPI_THV;

         global EPI_KWM;
         global EPI_KS;
         global EPI_KSO;  
         global EPI_UWM;    
         global EPI_US;    
         global EPI_UU;  
         global EPI_USO;   

         EPI_TVP   =     1.4506; 
         EPI_TV1M  =    60.;  
         EPI_TV2M  =  1150.; 

         EPI_TWP   =   200.0;   

         EPI_TW1M  =    60.0;     
         EPI_TW2M  =    15.;  
         
         EPI_TS1   =    2.7342;  
         EPI_TS2   =   16.;     %The same with Flavio's paper
         EPI_TFI   =    0.11;    %The same with Flavio's paper
         %EPI_TO1   =  0.0055;  
         EPI_TO1   =  400.;    %The same with Flavio's paper
         %EPI_TO2   =  0.13; 
         EPI_TO2   =    6.  ;    %The same with Flavio's paper
         EPI_TSO1  =   30.0181; %The same with Flavio's paper
         EPI_TSO2  =    0.9957;  %The same with Flavio's paper

         %EPI_TSI   =  0.17;
         EPI_TSI   =    1.8875;  % We have TSI1 and TSI2 = TSI in Flavio's paper


         EPI_TWINF  =  0.07;    %The same with Flavio's paper
         EPI_THV    =  0.3;     %EPUM % The same of Flavio's paper
         EPI_THVM   =  0.006;   %EPUQ % The same of Flavio's paper
         EPI_THVINF =  0.006;   %EPUQ % The same of Flavio's paper
         EPI_THW    =  0.13;    %EPUP % The same of Flavio's paper
         EPI_THWINF =  0.006;    %EPURR % In Flavio's paper 0.13
         EPI_THSO   =  0.13;    %EPUP % The same of Flavio's paper
         EPI_THSI   =  0.13;    %EPUP % The same of Flavio's paper
         EPI_THO    =  0.006;    %EPURR % The same of Flavio's paper

         EPI_KWM    =  65.;     %The same of Flavio's paper
         EPI_KS     =  2.0994;  %The same of Flavio's paper
         EPI_KSO    =  2.0458;  %The same of Flavio's paper
         
         EPI_UWM    =  0.03;    %The same of Flavio's paper
         EPI_US     =  0.9087;  %The same of Flavio's paper
         EPI_UO     =  0.;     % The same of Flavio's paper
         EPI_UU     =  1.55;   % The same of Flavio's paper
         EPI_USO    =  0.65;   % The same of Flavio's paper
         
         ut1     = [];
         vt1     = [];
         wt1     = [];
         st1     = [];
         stimt1  = [];
      
         u = 0.0;
         v = 1.0;
         w = 1.0;
         s = 0.0;
         t1 = 0;
         t2 = 0;

         %for i=1:20000   
             %[u,v,w,s, t1, t2, stim] = nextStepNonlinear (u,v,w,s, t1, t2, 0.05);
         for i=1:50000   
             [u,v,w,s, t1, t2, stim] = nextStepNonlinear (u,v,w,s, t1, t2, 0.01);
             ut1(i) =    u;
             vt1(i) =    v;
             wt1(i) =    w;
             st1(i) =    s;
             stimt1(i)=  stim;     
         end
         
         
         %ph = plot(linspace(0,1000, 20000), [ut1; vt1; wt1; st1; stimt1]);
         ph = plot(linspace(0,500, 50000), [ut1; vt1; wt1; st1; stimt1]);
         legend('u state variable', 'v state variable', 'w state variable','s state variable', 'stimulus');
         xlabel('Time in milliseconds');
         title ('Minimal Resistor Model');
end


function [u,v,w,s, t1, t2, stim] = nextStepNonlinear (u,v,w,s, t1, t2, dt)
         global EPI_TVP; 
         global EPI_TV1M;  
         global EPI_TV2M; 

         global EPI_TWP;   

         global EPI_TW1M; %190    
         global EPI_TW2M;
         
         global EPI_TS1;
         global EPI_TS2;
         global EPI_TFI;
         global EPI_TO1;
         global EPI_TO2;
         global EPI_TSO1;
         global EPI_TSO2;

         global EPI_TSI;


         global EPI_TWINF;
         global EPI_THV;

         global EPI_KWM;
         global EPI_KS;
         global EPI_KSO;  
         global EPI_UWM;    
         global EPI_US;    
         global EPI_UU;  
         global EPI_USO;   


         %% Stimulating the cell at 0, 300, 700 milliseconds
         t1 = t1 + dt;
         t2 = t2 + dt;
         %stim = heaviside(t1 - 0)*(1 - heaviside(t2 - 1)) + heaviside(t1 - 300)*(1 - heaviside(t2 - 301)) + heaviside(t1 - 700)*(1 - heaviside(t2 - 701));
         stim = heaviside(t1 - 0)*(1 - heaviside(t2 - 1)) + heaviside(t1 - 600)*(1 - heaviside(t2 - 601)) + heaviside(t1 - 990)*(1 - heaviside(t2 - 991));
         
         
         if u < 0.006
              w = w + ((1.0 -(u/EPI_TWINF) - w)/(EPI_TW1M + (EPI_TW2M - EPI_TW1M) * 0.5 * (1.+tanh(EPI_KWM*(u-EPI_UWM)))))*dt;     
              v = v + ((1.0-v)/EPI_TV1M)*dt;
              s = s + ((((1.+tanh(EPI_KS*(u - EPI_US))) * 0.5) - s)/EPI_TS1)*dt;
              jfi = 0.0;
              jso = u/EPI_TO1;
              jsi = 0.0;  
              
         elseif u < 0.13
              w = w + ((0.94-w)/(EPI_TW1M + (EPI_TW2M - EPI_TW1M) * 0.5 * (1.+tanh(EPI_KWM*(u-EPI_UWM)))))*dt;
              v = v + (-v/EPI_TV2M)*dt;
              s = s +((((1.+tanh(EPI_KS*(u-EPI_US))) * 0.5) - s)/EPI_TS1)*dt;
              jfi = 0.0;
              jso = u/EPI_TO2;
              jsi = 0.0;
         
         elseif u < 0.3
              w = w + (-w/EPI_TWP)*dt;
              v = v + (-v/EPI_TV2M)*dt;
              s = s + ((((1.+tanh(EPI_KS*(u-EPI_US))) * 0.5) - s)/EPI_TS2)*dt;
              jfi = 0.0;
              jso = 1./(EPI_TSO1+((EPI_TSO2-EPI_TSO1)*(1.+tanh(EPI_KSO*(u - EPI_USO)))) * 0.5);
              jsi = -w * s/EPI_TSI;
         else
              w  = w + (-w/EPI_TWP)*dt;
              v  = v + (-v/EPI_TVP)*dt;
              s  = s +((((1.+tanh(EPI_KS*(u - EPI_US))) * 0.5) - s)/EPI_TS2)*dt;
                       
              jfi = -v * (u - EPI_THV) * (EPI_UU - u)/EPI_TFI;
              jso = 1./(EPI_TSO1+((EPI_TSO2 - EPI_TSO1)*(1.+tanh(EPI_KSO*(u - EPI_USO)))) * 0.5);
              jsi = -w * s/EPI_TSI;  
         end

         u = u  - (jfi+jso+jsi-stim)*dt;
                 
end


