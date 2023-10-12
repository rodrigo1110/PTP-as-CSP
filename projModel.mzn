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
array[1..num_activities] of var int: activity_patient_id;
array[1..num_activities] of var int: activity_start;
array[1..num_activities] of var int: activity_duration;
array[1..num_activities] of var int: activity_end;
array[1..num_activities] of var int: activity_vehicle;
array[1..num_activities] of var bool: activity_completed;

array[1..num_patients] of var int: requests;

include "alldifferent.mzn";
include "cumulative.mzn";

constraint forall(i,j in num_activities)(
  if_then_else(activity_patient_id[i]==activity_patient_id[j], activity_completed[i] == true /\ activity_completed[j] == true)
)

/*
constraint forall(i in num_vehicles) (
  cumulative(
    [activity_start[j] | j in num_patients where patient_start_location[j] == vehicle_start_location[j]],
    [activity_duration[j] | j in num_patients where patient_start_location[j] == vehicle_start_location[j]],
    [vehicle_capacity[i]] 
));*/

/*constraint maxWaitTime != num_locations;
constraint alldifferent(location_id);*/

solve satisfy;