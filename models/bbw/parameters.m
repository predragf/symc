% Configuration parameter to decide if we use division to calculate the slip rate
% 1 means to use division to calculate the slip ratio
% 0 means to use Stateflow to search the integer slip ratio from 0 to 100.
use_division = 0;

% The sampling period of Brak_Torq_Calculation
T_brake_pedal = 0.01;
% The sampling time of the global brake controller
T_brake_ctrl = 0.02;
% The sampling time of the Vehicle speed estimator
T_spd_est = 0.02;
% The sampling time of the ABS at each wheel
T_abs = 0.01;
% The sampling time of the vehicle dynamics
T_veh = 0.005;
% The fundamental simulation time
T_sim = min([T_brake_pedal T_brake_ctrl T_spd_est T_abs T_veh]);

%The weight of the vehicle in kg.
M=2000; 

%The gravity acceleration
g=9.8; %(m/s^2)

%The weight of a wheel.
m=20;

%The radius of the wheel in meter
R=0.5;

%Moment of inertia of the wheele.
I=m*R^2/2;

%The maximal brake torque in Nm when the brake pedal is at 100% position
maxBrakeTorque=3000; % (Nm)

% BrakeTorque distribution on four wheels: 
% Rear Right, Rear Left, Front Right, and Front Left

distrib=[0.31; 0.29; 0.21; 0.19];

% The threshold slip ratio to turn on ABS and release the brake
% Because the ABS controller uses estimated vehicle speed to calculate the
% ratio, the estimated ratio is always smaller than the real slip ratio
% during braking. This threshold value in the ABS controller must be
% smaller than 20% to reduce the actual slip ratio
slip_abs_on = 0.1;

%The peak value of the friction coefficient, reached at slip rate=0.2
f_max=0.3;
slip_max=0.2;

%The limit of the friction coefficient when the slip rate approaches infinity
f_limit=0.2;
slip_limit=0.3;

% Friction Force Table
Fc_table_x = 100*[0 slip_max slip_limit 1];     % Convert to percentage
Fc_table_y = [0 f_max f_limit f_limit]*M*g/4;

%Initial speed
v0=0; %(m/s), equals to 0km/h
w0=v0/R; %(rad/s)

% Maximal speed
v_max=round(200/3.6); % m/s
w_max=round(v_max/R);  % rad/s