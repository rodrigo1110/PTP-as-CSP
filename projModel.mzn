include "alldifferent.mzn";
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
%array[1..num_activities] of var int: activity_patient;
array[1..num_activities] of var int: activity_start;
array[1..num_activities] of var int: activity_duration;
array[1..num_activities] of var int: activity_end;
array[1..num_activities] of var int: activity_vehicle;
array[1..num_activities] of var bool: activity_completed;

var int: maximumRequestsObjective = sum(i in 1..num_patients)(activity_completed[i] == true /\ activity_completed[i+num_patients] == true);

%array[1..num_patients] of var int: requests;

%Auxiliar functions
function int: patientIndex(int : activity_patient_index) =
  if activity_patient_index > num_patients then activity_patient_index - num_patients else activity_patient_index endif
;
function var int: vehicleIndex(var int : activity_vehicle) =
  if patient_id[1] > activity_vehicle then activity_vehicle - num_locations + 1 else activity_vehicle - num_locations - num_patients + 1 endif
;

%Missing in every constraint an option to put activity_completed[i] == false if all conditions fail.
%Correct vehicleIndex function because sometimes vehicles come after patients (very_easy_1)
%Add domain restriction to limit duration from zero to MaxWaitTime?

%Domain constraints
constraint forall(i in 1..num_activities)( 
  if activity_start_location[i] == -1 \/ activity_end_location[i] == -1 then 
    activity_completed[i] == true /\ activity_start[i] == -1 /\ activity_end[i] == -1 /\ activity_vehicle[i] == -1 /\ activity_duration[i] == 0
  else activity_vehicle[i] in array2set(vehicle_id) /\ activity_start[i] >= 0 /\ activity_start[i] < 1440 /\ 
    activity_end[i] > activity_start[i] /\ activity_duration[i] == activity_end[i] - activity_start[i] /\ activity_duration[i] < maxWaitTime
  %/\ activity_start[i]!=-1 /\ activity_end[i] != -1 /\ activity_vehicle[i] != -1
  endif
);

/*
constraint forall(i in 1..num_activities)( %General time boundaries (Maybe condense in Logical time period constraints).
  activity_start[i] >= -1 /\ activity_start[i] < 1440 /\ (activity_end[i] == -1 \/ activity_end[i] > 0) /\ activity_end[i] <= 1440 /\ activity_end[i] >= activity_start[i]
);*/
constraint forall(i in 1..num_patients)( %Logical time period - Forward activities
  if patient_start_location[i]!=-1 then
    %activity_start[i] <= (rdvTime[i] - distMatrix[patient_start_location[i]+1, patient_destination[i]+1] - srvDuration[i]) /\ 
    %activity_end[i] >= (rdvTime[i] - maxWaitTime) /\ activity_end[i] <= rdvTime[i] endif
    activity_start[i] >= rdvTime[i] - maxWaitTime /\
    activity_end [i] <= rdvTime[i] endif
);
constraint forall(i in 1..num_patients)( %Logical time period - Backward activities
  if patient_end_location[i] != -1 then
    %activity_start[i+num_patients] >= (rdvTime[i] + rdvDuration[i]) /\  activity_start[i+num_patients] <= (rdvTime[i] + rdvDuration[i] + maxWaitTime) /\
    %activity_end[i+num_patients] >= (rdvTime[i] + rdvDuration[i] + distMatrix[patient_destination[i]+1, patient_end_location[i]+1]) endif
    activity_start[i+num_patients] >= rdvTime[i] + rdvDuration[i] /\
    activity_end[i+num_patients] <= rdvTime[i] + rdvDuration[i] + maxWaitTime endif
);    

%Add restriction that if vehicle in position i of activities, then it has to have satisfied the corresponding request(front or back) of patient i.
/*
constraint forall(i in 1..num_activities)( %Valid duration
  activity_duration[i] == activity_end[i] - activity_start[i]
);
constraint forall(i in 1..num_activities)( %Valid vehicle ids
  activity_vehicle[i] in array2set(vehicle_id) \/ activity_vehicle[i] == -1 %/\ activity_patient[i] in array2set(patient_id)
);*/
/*constraint forall(i,j in 1..num_activities)( %Logical valid duration (Necessary or just use intra-activity time travel consistency?)
  let{
    var int: patientIndex = activity_patient[i] - num_vehicles - num_locations + 1;
  } in
  if i<j /\ activity_patient[i]==activity_patient[j] then
    if patient_start_location[patientIndex] != -1 then
      activity_duration[i] >= distMatrix[patient_start_location[patientIndex],patient_destination[patientIndex]]
    endif /\
    if patient_end_location[patientIndex] != -1 then
       activity_duration[j] >= distMatrix[patient_destination[patientIndex],patient_end_location[patientIndex]]
    endif  
  endif
);*/

/*constraint forall(i in 1..num_activities)( %Valid number of patient participations
  count(activity_patient, activity_patient[i]) <= 2
);*/


%Correctness constraints
/*
constraint forall(i in 1..num_patients)( %Forward and backward activity must be both completed
  if patient_start_location[i] != -1 /\ patient_end_location[i] != -1 then activity_completed[i] == true /\ activity_completed[i+num_patients] == true
  else activity_completed[i] == true \/ activity_completed[i+num_patients] == true  endif
);*/
constraint forall(i in 1..num_patients)( %Forward and backward activity status must be equal
  if patient_start_location[i] != -1 /\ patient_end_location[i] != -1 then activity_completed[i] == activity_completed[i+num_patients] endif
);



%Other constraints
constraint forall(i in 1..num_patients)( %Intra-Activity time travel consistency - Forward Activities
   if patient_start_location[i] != -1 then activity_duration[i] >= distMatrix[patient_start_location[i]+1, patient_destination[i]+1] endif
);
constraint forall(i in 1..num_patients)( %Intra-Activity time travel consistency - Backward Activities
  if patient_end_location[i] != -1 then activity_duration[i+num_patients] >= distMatrix[patient_destination[i]+1, patient_end_location[i]+1] endif
);

constraint if sameVehicleBackward then %Same vehicle forward/backward
  forall(i in 1..num_patients)(
    if patient_start_location[i] != -1 /\ patient_end_location[i] != -1 then activity_vehicle[i] == activity_vehicle[i+num_patients] \/ activity_completed[i] == false
    endif
  )
  endif;

constraint forall(i in 1..num_activities)( %canTake constraint (cheat - assume max n of categories is 3
  let {
    int: patientIndex = patientIndex(i);
    var int: vehicleIndex = vehicleIndex(activity_vehicle[i]);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 then
    vehicle_canTake[vehicleIndex,1] == patient_category[patientIndex] \/ 
    vehicle_canTake[vehicleIndex,2] == patient_category[patientIndex] \/
    vehicle_canTake[vehicleIndex,3] == patient_category[patientIndex]
  endif
  %count(vehicle_canTake[vehicleIndex(activity_vehicle[i]),..], patient_category[patientIndex(i)]) == 1 
  %patient_category[patientIndex(i)] in array2set(vehicle_canTake[vehicleIndex(activity_vehicle[i]),..])
);


constraint forall(i in 1..num_activities)( %Vehicle availability - Forward activities(start)(cheat - assume max availability periods is 2) (Missing end check for forward)
  let{
    var int: vehicleIndex = vehicleIndex(activity_vehicle[i]);
    /*var int: vehicleDeslocationStart = if vehicle_start_location[vehicleIndex]!=-1 then distMatrix[vehicle_start_location[vehicleIndex]+1, activity_start_location[i]+1] else 0 endif;
    var int: vehicleDeslocationEnd = if vehicle_end_location[vehicleIndex]!=-1 then distMatrix[activity_end_location[i]+1, vehicle_end_location[vehicleIndex]+1] else 0 endif;*/
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 then
    (activity_start[i] >= vehicle_availability_start[vehicleIndex, 1] + distMatrix[vehicle_start_location[vehicleIndex]+1, activity_start_location[i]+1]  /\
    activity_end[i] <= vehicle_availability_end[vehicleIndex, 1] - distMatrix[activity_end_location[i]+1, vehicle_end_location[vehicleIndex]+1])  \/  
    (activity_start[i] >= vehicle_availability_start[vehicleIndex, 2] + distMatrix[vehicle_start_location[vehicleIndex]+1, activity_start_location[i]+1] /\
    activity_end[i] <= vehicle_availability_end[vehicleIndex, 2] - distMatrix[activity_end_location[i]+1, vehicle_end_location[vehicleIndex]+1])  
    \/ activity_completed[i] == false %Keep or remove based on test score (assumption in google docs should be true and make this line pointless - (counter custom4 test
  endif
);
  /*if patient_start_location[i] != -1 then 
    if vehicle_start_location[vehicleIndex]!=-1 then
      activity_start[i] >= vehicle_availability_start[vehicleIndex, 1] + distMatrix[vehicle_start_location[vehicleIndex]+1, patient_start_location[i]+1] \/
      activity_start[i] >= vehicle_availability_start[vehicleIndex, 2] + distMatrix[vehicle_start_location[vehicleIndex]+1, patient_start_location[i]+1]
    else activity_start[i] >= vehicle_availability_start[vehicleIndex, 1] \/ activity_start[i] >= vehicle_availability_start[vehicleIndex, 2] endif
  endif*/
/*
constraint forall(i in 1..num_patients)( %Vehicle availability - Forward activities(end) (working but very slow) (Missing same two for backward activities.
  let{
    var int: vehicleIndex = vehicleIndex(activity_vehicle[i]);
  } in
  if patient_end_location[i] != -1 then 
    if vehicle_end_location[vehicleIndex]!=-1 then
      activity_end[i] <= vehicle_availability_end[vehicleIndex, 1] - distMatrix[patient_destination[i]+1, vehicle_end_location[vehicleIndex]+1] \/
      activity_end[i] <= vehicle_availability_end[vehicleIndex, 2] - distMatrix[patient_destination[i]+1, vehicle_end_location[vehicleIndex]+1]
    else activity_end[i] <= vehicle_availability_end[vehicleIndex, 1] \/ activity_end[i] >= vehicle_availability_end[vehicleIndex, 2] endif
  endif
);*/


constraint forall(i in 1..num_vehicles)(%Cumulative resource - (Come after or before inter-activity constraints?)(Remove activities where pat_start/end = -1 or if status==fals?
  %if (i <= num_patients /\ patient_start_location[patientIndex(i)] != -1) \/ (i > num_patients /\ patient_end_location[patientIndex(i)] != -1) then
    let{
      array[1..num_activities] of int : patientLoads = patient_load ++ patient_load
    } in 
    cumulative( %Cumulative resource
      activity_start, 
      activity_duration, 
      patientLoads,
      vehicle_capacity[i])
  %endif
);


%Inter-acivity time travel consistency constraints 
constraint forall(i,j in 1..num_activities where i!=j)( %No start overlap
  let {
    int: patientIndexI = patientIndex(i);
    int: patientIndexJ = patientIndex(j);
  } in
  if activity_start_location[i] != -1 /\ activity_end_location[i] != -1 /\ activity_start_location[j] != -1 /\ activity_end_location[j] != -1 then
    %if activity_vehicle[i] == activity_vehicle[j] then
      %(activity_vehicle[i] == activity_vehicle[j] /\ 
      (activity_start[j] - activity_start[i] >= distMatrix[activity_start_location[i]+1, activity_start_location[j]+1] + srvDuration[patientIndexI] \/ 
      activity_start[i] - activity_start[j] >= distMatrix[activity_start_location[j]+1, activity_start_location[i]+1] + srvDuration[patientIndexJ]) \/ 
      activity_vehicle[i] != activity_vehicle[j] \/ activity_completed[i] == false \/ activity_completed[j] == false
      
      %activity_vehicle[i] != activity_vehicle[j] \/ 
    endif
  %endif
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


/*    
    if i <= num_patients /\ j <= num_patients /\ patient_start_location[patientIndexI] != -1 /\ patient_start_location[patientIndexJ] != -1 then %Ai and Aj forward activities
      activity_start[j] - activity_start[i] >= distMatrix[patient_start_location[patientIndexI]+1, patient_start_location[patientIndexJ]+1] + srvDuration[patientIndexI] \/
      activity_start[i] - activity_start[j] >= distMatrix[patient_start_location[patientIndexJ]+1, patient_start_location[patientIndexI]+1] + srvDuration[patientIndexJ]
      
    else if i > num_patients /\ j <= num_patients /\ patient_end_location[patientIndexI] !=- 1 /\ patient_start_location[patientIndexJ] != -1 then %Ai backward Aj forward
      activity_start[j] - activity_start[i] >= distMatrix[patient_destination[patientIndexI]+1, patient_start_location[patientIndexJ]+1] + srvDuration[patientIndexI] \/
      activity_start[i] - activity_start[j] >= distMatrix[patient_start_location[patientIndexJ]+1, patient_destination[patientIndexI]+1] + srvDuration[patientIndexJ]
      
    else if i <= num_patients /\ j > num_patients /\ patient_start_location[patientIndexI] !=- 1 /\ patient_end_location[patientIndexJ] != -1 then %Ai forward Aj backward
      activity_start[j] - activity_start[i] >= distMatrix[patient_start_location[patientIndexI]+1, patient_destination[patientIndexJ]+1] + srvDuration[patientIndexI] \/
      activity_start[i] - activity_start[j] >= distMatrix[patient_destination[patientIndexJ]+1, patient_start_location[patientIndexI]+1] + srvDuration[patientIndexJ]
      
    else if i > num_patients /\ j > num_patients /\ patient_end_location[patientIndexI] !=- 1 /\ patient_end_location[patientIndexJ] != -1 then %Ai backward Aj backward
      activity_start[j] - activity_start[i] >= distMatrix[patient_destination[patientIndexI]+1, patient_destination[patientIndexJ]+1] + srvDuration[patientIndexI] \/
      activity_start[i] - activity_start[j] >= distMatrix[patient_destination[patientIndexJ]+1, patient_destination[patientIndexI]+1] + srvDuration[patientIndexJ]  
   endif endif endif endif */
  %endif  
%);


/*constraint forall(i,j in 1..num_activities where i<j)( %Inter-activity time travel consistency - start time need to control i and j values for check to only be done once
  let{
    var int: activityOrigin_i = activity_locations[i,1]+1;
    var int: activityOrigin_j = activity_locations[j,1]+1;
    var int: activityPatient_i = activity_patient[i] - num_locations - num_vehicles + 1;
    var int: activityPatient_j = activity_patient[j] - num_locations - num_vehicles + 1;
  } in
  if i!=j /\ activity_vehicle[i]==activity_vehicle[j] then activity_start[j] - activity_start[i] >= (distMatrix[activityOrigin_i,activityOrigin_j] + srvDuration[activityPatient_i])
  \/ activity_start[i] - activity_start[j] >= (distMatrix[activityOrigin_j,activityOrigin_i] + srvDuration[activityPatient_j]) endif 
  
);*/


/*
constraint forall(i in 1..num_activities)( %Vehicle availability 
  forall(j in 1..num_availability)( 
    if vehicle_availability_start[vehicleIndex, j] != -1 then %Think of way to ensure that activity_start and end always within at least an availability period
      if activity_start[i] >= vehicle_availability_start[vehicleIndex,j] + distMatrix[vehicle_start_location[vehicleIndex], patient_start_location[patientIndex]] /\
      activity_end[i] <= vehicle_availability_end[vehicleIndex,j] + distMatrix[patient_destination[patientIndex], vehicle_end_location[vehicleIndex]] then true else false
      endif
    endif
));*/

solve maximize maximumRequestsObjective;