bool: sameVehicleBackward;
int: maxWaitTime;

int: num_locations;
int: num_vehicles;
int: num_patients;
int: num_canTake;
int: num_availability;

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

include "alldifferent.mzn";
include "cumulative.mzn";

/*constraint forall(i in vehicles) (
  cumulative(
    
));*/

/*constraint maxWaitTime != num_locations;
constraint alldifferent(location_id);*/

solve satisfy;