function [out] = prostate ()

         global alphax; 
         global alphay;  
         global betax; 
         global betay;   
         global k1;   
         global k2;
         global k3;
         global k4;
         global m1;
         global z0;
         global t;
         global r1;
         global r0;

         global c1;
         global c2;
         global c3;
         
         global scale;
         global u;
  

         alphax = 0.0204; 
         alphay = 0.0242;  
         betax = 0.0076; 
         betay = 0.0168;   
         k1 = 0.0;   
         k2 = 2.0;
         k3 = 0.8;
         k4 = 0.5;
         m1 = 0.00005;
         z0 = 30.0; % init
         t = 12.5;
         r1 = 15.0;
         r0 = 10.0 ;

         c1 = 0.0;
         c2 = 0.0;
         c3 = 0.0;
         
         scale = 50.0;
         u = 1.0;
         % d	1.0	// Hypothesis (i) 1.0; (ii) (1 - ((1 - (betay / alphay)) * (z / z0))) (iii) (1 - (z / z0))
         
                  
         xt1     = [];
         yt1     = [];
         zt1     = [];
         ut1     = [];

      
         x = 15.0;
         y = 0.1;
         z = z0;
         v = x + y;

         for i=1:20000   
             [x,y,z,v] = nextStepNonlinear (x,y,z,v, 0.001);
             xt1(i) =    x;
             yt1(i) =    y;
             zt1(i) =    z;
             vt1(i) =    v;     
         end
         
         ph = plot(linspace(0,1000, 20000), [xt1; yt1; zt1; vt1]);
         legend('x (AD cells)', 'y (AI cells)', 'z (Androgen)','v (PSA)');
         xlabel('Time (day)');
         title ('Prosate Cancer Model');
end


function [x,y,z,v] = nextStepNonlinear (x,y,z,v, dt)
         global alphax; 
         global alphay;  
         global betax; 
         global betay;   
         global k1;   
         global k2;
         global k3;
         global k4;
         global m1;
         global z0;
         global t;
         global r1;
         global r0;

         global c1;
         global c2;
         global c3;
         
         global scale;
         global u;

         Gx = ((alphax * (k1 + ((1.0 - k1) * (z / (z + k2))))) - (betax * (k3 + (1 - k3) * (z / (z + k4)))));
         Gy = ((alphay * (1.0 - (1.0 * (z / z0)))) - betay);
         Mxy = (m1 * (1.0 - (z / z0)));
         
         % on-treatment
         if v >= r1 && (((((Gx - Mxy) * x) + c1 * x) + (((Mxy * x) + Gy * y ) + c2 * y)) > 0)
              u = 1;
         % off-treatment     
         elseif v <= r0 && (((((Gx - Mxy) * x) + c1 * x) + (((Mxy * x) + Gy * y ) + c2 * y)) < 0)
              u = 0;
         end
         
         
         x = x + scale * (((Gx - Mxy) * x) + c1 * x)*dt;     
         y = y + scale * (((Mxy * x) + Gy * y ) + c2 * y)*dt;
         z = z + scale * (((z0 * (1 - u) - z) / t) + c3 * z)*dt;
         v = v + scale * ((((Gx - Mxy) * x) + c1 * x) + (((Mxy * x) + Gy * y ) + c2 * y))*dt;                   
end


