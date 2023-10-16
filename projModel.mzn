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


%Decision variables
array[1..num_activities] of var int: activity_patient;
array[1..num_activities] of var int: activity_start;
array[1..num_activities] of var int: activity_duration;
array[1..num_activities] of var int: activity_end;
array[1..num_activities] of var int: activity_vehicle;
array[1..num_activities] of var bool: activity_completed;
array[1..num_activities,1..num_locations] of var int: activity_locations;

array[1..num_patients] of var int: requests;



%Domain constraints
constraint forall(i in 1..num_activities)( %General time period
  activity_start[i] >= 0 /\ activity_start[i] < 1440 /\ activity_end[i] > 0 /\ activity_end[i] <= 1440
);
constraint forall(i,j in 1..num_activities)( %Logical time period
  let{
    var int: patientIndex = activity_patient[i] - num_vehicles - num_locations + 1;
  } in
  if i<j /\ activity_patient[i]==activity_patient[j] then activity_start[i] <= (rdvTime[patientIndex] - maxWaitTime) /\ 
    activity_start[j] >= (rdvTime[patientIndex] + rdvDuration[patientIndex] + maxWaitTime) /\ 
    activity_end[i] <= (rdvTime[patientIndex] - maxWaitTime) /\ 
    activity_end[j] >= (rdvTime[patientIndex] + rdvDuration[patientIndex] + maxWaitTime)
  endif
);

constraint forall(i in 1..num_activities)( %Valid duration
  activity_duration[i] == activity_end[i] - activity_start[i] /\ activity_duration[i] > 0
);
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

constraint forall(i in 1..num_activities)( %Valid vehicle and patient ids
  activity_vehicle[i] in array2set(vehicle_id) /\ activity_patient[i] in array2set(patient_id)
);
constraint forall(i in 1..num_activities, j in 1..num_locations)( %Valid location ids
  activity_locations[i,j] in array2set(location_id) %/\ all_different(activity_locations[i,..])
);
constraint forall(i in 1..num_activities)( %Valid number of patient participations
  count(activity_patient, activity_patient[i]) <= 2
);


%Correctness constraints
constraint forall(i,j in 1..num_activities)( %Forward and backward activity must be both completed
  if i!=j /\ activity_patient[i]==activity_patient[j] then activity_completed[i] == true /\ activity_completed[j] == true endif
);
constraint forall(i,j in 1..num_activities)( %Forward and backward activity status must be equal
  if i!=j /\ activity_patient[i]==activity_patient[j] then activity_completed[i] == activity_completed[j] endif
);

/*constraint forall(i,j in 1..num_activities)( %Inter-activity time travel consistency - start time need to control i and j values for check to only be done once
  let{
    var int: activityOrigin_i = activity_locations[i,1]+1;
    var int: activityOrigin_j = activity_locations[j,1]+1;
    var int: activityPatient_i = activity_patient[i] - num_locations - num_vehicles + 1;
    var int: activityPatient_j = activity_patient[j] - num_locations - num_vehicles + 1;
  } in
  if i!=j /\ activity_vehicle[i]==activity_vehicle[j] then activity_start[j] - activity_start[i] >= (distMatrix[activityOrigin_i,activityOrigin_j] + srvDuration[activityPatient_i])
  \/ activity_start[i] - activity_start[j] >= (distMatrix[activityOrigin_j,activityOrigin_i] + srvDuration[activityPatient_j]) endif 
  
);*/
constraint forall(i in 1..num_activities)( %Intra-Activity time travel consistency
   activity_duration[i] >= distMatrix[activity_locations[i,1]+1,activity_locations[i, length(activity_locations[i,..])]+1]
);/*
constraint forall(i in 1..num_activities)( %Vehicle availability
  forall(j in 1..num_availability)( 
    let{
      var int: vehicleIndex = activity_vehicle[i] - num_locations + 1;
      var int: patientIndex = activity_patient[i] - num_locations - num_vehicles + 1
    } in
    if vehicle_availability_start[vehicleIndex, j] != -1 then %Think of way to ensure that activity_start and end always within at least an availability period
      if activity_start[i] >= vehicle_availability_start[vehicleIndex,j] + distMatrix[vehicle_start_location[vehicleIndex], patient_start_location[patientIndex]] /\
      activity_end[i] <= vehicle_availability_end[vehicleIndex,j] + distMatrix[patient_destination[patientIndex], vehicle_end_location[vehicleIndex]] then true else false
      endif
    endif
));*/

constraint if sameVehicleBackward then %Same vehicle forward/backward
  forall(i,j in 1..num_activities)(
    if i!=j /\ activity_patient[i]==activity_patient[j] then activity_vehicle[i] == activity_vehicle[j]
    endif
  )
  else true
  endif;
/*
constraint forall(i in num_vehicles) ( %Vehicle capacity limit
  cumulative(
    [activity_start[j] | j in num_patients where patient_start_location[j] == vehicle_start_location[j]],
    [activity_duration[j] | j in num_patients where patient_start_location[j] == vehicle_start_location[j]],
    [vehicle_capacity[i]] 
));*/

/*constraint maxWaitTime != num_locations;
constraint alldifferent(location_id);*/

solve satisfy;