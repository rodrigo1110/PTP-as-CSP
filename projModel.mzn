include "cumulative.mzn";

%Parameters
bool: sameVehicleBackward;
int: maxWaitTime;

int: num_locations;
int: num_vehicles;
int: num_patients;
int: num_canTake;
int: num_availability;
int: num_activities = num_patients * 2;

set of int: locations = 1..num_locations;
set of int: vehicles = 1..num_vehicles;
set of int: patients = 1..num_patients;
array[locations,locations] of int: distMatrix;

%Location
array[locations] of int: location_id;
array[locations] of int: location_category;

%Vehicle
array[vehicles] of int: vehicle_id;
array[vehicles,1..num_canTake] of int: vehicle_canTake;
array[vehicles] of int: vehicle_start_location;
array[vehicles] of int: vehicle_end_location;
array[vehicles] of int: vehicle_capacity;
array[vehicles,1..num_availability] of int: vehicle_availability_start;
array[vehicles,1..num_availability] of int: vehicle_availability_end;

%Patient
array[patients] of int : patient_id;
array[patients] of int : patient_category;
array[patients] of int : patient_load;
array[patients] of int : patient_start_location;
array[patients] of int : patient_destination;
array[patients] of int : patient_end_location;
array[patients] of int : rdvTime;
array[patients] of int : rdvDuration;
array[patients] of int : srvDuration;

%Auxiliary variables
array[1..num_activities] of int: activity_start_location = patient_start_location ++ patient_destination;
array[1..num_activities] of int: activity_end_location = patient_destination ++ patient_end_location;

%Decision variables
array[1..num_activities] of var int: activity_start;
array[1..num_activities] of var int: activity_duration;
array[1..num_activities] of var int: activity_end;
array[1..num_activities] of var int: activity_vehicle;
array[1..num_activities] of var bool: activity_completed;

var int: maximumRequestsObjective = sum(i in 1..num_patients)(activity_completed[i] == true /\ activity_completed[i+num_patients] == true);


%-----------------------------------------Auxiliary functions------------------------------------------

function int: patientIndex(int : activity_patient_index) =
  if activity_patient_index > num_patients then activity_patient_index - num_patients else activity_patient_index endif
;
function var int: vehicleIndex(var int : activity_vehicle) =
  if patient_id[1] > activity_vehicle then activity_vehicle - num_locations + 1 else activity_vehicle - num_locations - num_patients + 1 endif
;


%----------------------------------------Constraints---------------------------------------------------

%Domain constraints
constraint forall(i in 1..num_activities)( 
  if activity_start_location[i] == -1 \/ activity_end_location[i] == -1 then 
    activity_completed[i] == true /\ activity_start[i] == -1 /\ activity_end[i] == -1 /\ activity_vehicle[i] == -1 /\ activity_duration[i] == 0
  else activity_vehicle[i] in array2set(vehicle_id) /\ activity_start[i] >= 0 /\ activity_start[i] < 1440 /\ 
    activity_end[i] > activity_start[i] /\ activity_duration[i] == activity_end[i] - activity_start[i] /\ activity_duration[i] < maxWaitTime
  endif
);

%Logical time periods
constraint forall(i in 1..num_patients)( %Forward activities
  if patient_start_location[i]!=-1 then
    activity_start[i] >= rdvTime[i] - maxWaitTime /\
    activity_end [i] <= rdvTime[i] endif
);
constraint forall(i in 1..num_patients)( %Backward activities
  if patient_end_location[i] != -1 then
    activity_start[i+num_patients] >= rdvTime[i] + rdvDuration[i] /\
    activity_end[i+num_patients] <= rdvTime[i] + rdvDuration[i] + maxWaitTime endif
);    



%Correctness constraint
constraint forall(i in 1..num_patients)( %Forward and backward activity status must be equal
  if patient_start_location[i] != -1 /\ patient_end_location[i] != -1 then activity_completed[i] == activity_completed[i+num_patients] endif
);



%Intra-Activity time travel consistency
constraint forall(i in 1..num_patients)( %Forward Activities
   if patient_start_location[i] != -1 then activity_duration[i] >= distMatrix[patient_start_location[i]+1, patient_destination[i]+1] endif
);
constraint forall(i in 1..num_patients)( %Backward Activities
  if patient_end_location[i] != -1 then activity_duration[i+num_patients] >= distMatrix[patient_destination[i]+1, patient_end_location[i]+1] endif
);


%Same vehicle forward/backward
constraint if sameVehicleBackward then 
  forall(i in 1..num_patients)(
    if patient_start_location[i] != -1 /\ patient_end_location[i] != -1 then activity_vehicle[i] == activity_vehicle[i+num_patients] \/ activity_completed[i] == false
    endif
  )
  endif;
  
  
%canTake constraint 
constraint forall(i in 1..num_activities)( 
  let {
    int: patientIndex = patientIndex(i);
    var int: vehicleIndex = vehicleIndex(activity_vehicle[i]);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 then
    vehicle_canTake[vehicleIndex,1] == patient_category[patientIndex] \/ 
    vehicle_canTake[vehicleIndex,2] == patient_category[patientIndex] \/
    vehicle_canTake[vehicleIndex,3] == patient_category[patientIndex]
  endif
);


%Vehicle availability constraint
constraint forall(i in 1..num_activities)( 
  let{
    var int: vehicleIndex = vehicleIndex(activity_vehicle[i]);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 then
    (activity_start[i] >= vehicle_availability_start[vehicleIndex, 1] + distMatrix[vehicle_start_location[vehicleIndex]+1, activity_start_location[i]+1]  /\
    activity_end[i] <= vehicle_availability_end[vehicleIndex, 1] - distMatrix[activity_end_location[i]+1, vehicle_end_location[vehicleIndex]+1])  \/  
    (activity_start[i] >= vehicle_availability_start[vehicleIndex, 2] + distMatrix[vehicle_start_location[vehicleIndex]+1, activity_start_location[i]+1] /\
    activity_end[i] <= vehicle_availability_end[vehicleIndex, 2] - distMatrix[activity_end_location[i]+1, vehicle_end_location[vehicleIndex]+1])  
    \/ activity_completed[i] == false 
  endif
);
  

%Cumulative resouce - vehicle capacity
constraint forall(i in 1..num_vehicles)(%Cumulative resource - (Come after or before inter-activity constraints?)
    let{
      array[1..num_activities] of int : patientLoads = patient_load ++ patient_load
    } in 
    cumulative(
      activity_start, 
      activity_duration, 
      patientLoads,
      vehicle_capacity[i])
);



%Inter-acivity time travel consistency constraints 
constraint forall(i,j in 1..num_activities where i!=j)( %No start overlap
  let {
    int: patientIndexI = patientIndex(i);
    int: patientIndexJ = patientIndex(j);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 /\ activity_start_location[j] != -1 /\ activity_end_location[j] != -1 then
    (activity_start[j] - activity_start[i] >= distMatrix[activity_start_location[i]+1, activity_start_location[j]+1] + srvDuration[patientIndexI] \/ 
    activity_start[i] - activity_start[j] >= distMatrix[activity_start_location[j]+1, activity_start_location[i]+1] + srvDuration[patientIndexJ]) \/ 
    activity_vehicle[i] != activity_vehicle[j] \/ activity_completed[i] == false \/ activity_completed[j] == false
  endif
);
constraint forall(i,j in 1..num_activities where i!=j)( %No end overlap
  let {
    int: patientIndexI = patientIndex(i);
    int: patientIndexJ = patientIndex(j);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 /\ activity_start_location[j] != -1 /\ activity_end_location[j] != -1 then
    (activity_end[j] - activity_end[i] >= distMatrix[activity_end_location[i]+1, activity_end_location[j]+1] + srvDuration[patientIndexJ] \/ 
    activity_end[i] - activity_end[j] >= distMatrix[activity_end_location[j]+1, activity_end_location[i]+1] + srvDuration[patientIndexI]) \/ 
    activity_vehicle[i] != activity_vehicle[j] \/ activity_completed[i] == false \/ activity_completed[j] == false
  endif
);
constraint forall(i,j in 1..num_activities where i!=j)( %Min travel time
  let {
    int: patientIndexI = patientIndex(i);
    int: patientIndexJ = patientIndex(j);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 /\ activity_start_location[j] != -1 /\ activity_end_location[j] != -1 then
    (activity_start[j] - activity_end[i] >= distMatrix[activity_end_location[i]+1, activity_start_location[j]+1]  \/ 
    activity_end[i] - activity_start[j] >= distMatrix[activity_start_location[j]+1, activity_end_location[i]+1] + srvDuration[patientIndexJ] + srvDuration[patientIndexI]) \/ 
    activity_vehicle[i] != activity_vehicle[j] \/ activity_completed[i] == false \/ activity_completed[j] == false
  endif
);
constraint forall(i,j in 1..num_activities where i!=j)( %Min travel time 
  let {
    int: patientIndexI = patientIndex(i);
    int: patientIndexJ = patientIndex(j);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 /\ activity_start_location[j] != -1 /\ activity_end_location[j] != -1 then
      (activity_end[j] - activity_start[i] >= distMatrix[activity_start_location[i]+1, activity_end_location[j]+1] + srvDuration[patientIndexI] + srvDuration[patientIndexJ]) \/ 
      activity_start[i] - activity_end[j] >= distMatrix[activity_end_location[j]+1, activity_start_location[i]+1]  \/ 
      activity_vehicle[i] != activity_vehicle[j] \/ activity_completed[i] == false \/ activity_completed[j] == false
  endif
);



solve maximize maximumRequestsObjective;