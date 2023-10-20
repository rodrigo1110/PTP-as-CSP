import sys
import json
from minizinc import Instance, Model, Solver



class Trip:
    def __init__(self, origin, destination, arrivalTime, patients):
        self.origin = origin
        self.destination = destination
        self.arrivalTime = arrivalTime
        self.patients = patients



#---------------------------------------Auxiliary functions---------------------------------------



def convert_str_to_mins(timestr):
    time_elements = timestr.split('h')
    return (int(time_elements[0])*60) + int(time_elements[1]) 
def convert_mins_to_str(mins):
    hours = mins//60
    minutes = mins%60
    return "{:02d}".format(hours) + 'h' + "{:02d}".format(minutes)



#-------------------------------------Auxiliary functions - Minizinc result processing---------------------------------------



#Sort chronologically patients transported by a given vehicle according to order of requests
def sort_vehicle_patients_chronologically(vehiclePatients, vehiclePatientsStartTimes):
    return [x for _, x in sorted(zip(vehiclePatientsStartTimes,vehiclePatients))]

#Return trips of patients that a vehicle is waiting for at a given hospital
def obtain_return_trips_after_wait(first_origin):
    return_trips, trip_patients = [], []
    for k in range(len(patientsWaiting)):
        if(len(return_trips) == 0):
            trip_origin = first_origin
        else:
            trip_origin = return_trips[k-1].destination
        i = patientsWaiting[k]
        trip_destination = activity_ends[i]
        trip_arrivalTime = convert_mins_to_str(activity_end_time[i] + srvDurations[i]) 
        for j in range(k,len(patientsWaiting)):
            trip_patients.append(patientIDs[patientsWaiting[j]]) 
        return_trips.append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
        trip_patients = []
   
    return return_trips
    
#Trips without patients where another patient has to be picked-up
def check_if_empty_trip_needed(curr_patient, prev_patient, trip_origin, prev_arrivalTime):
    if trip_origin != activity_starts[curr_patient]:
        if activity_start_time[curr_patient] - activity_start_time[prev_patient] != distMatrix[activity_starts[curr_patient]][activity_starts[prev_patient]] + srvDurations[curr_patient]:
            trip_destination = activity_starts[curr_patient]
            if activity_start_time[curr_patient] - convert_str_to_mins(prev_arrivalTime) < distMatrix[trip_origin][trip_destination]:
                trip_arrival = convert_mins_to_str(distMatrix[trip_origin][trip_destination] + convert_str_to_mins(prev_arrivalTime) + srvDurations[prev_patient])
            else:
                trip_arrival = convert_mins_to_str(activity_start_time[curr_patient])
            trip_patients = []
            return Trip(trip_origin, trip_destination, trip_arrival, trip_patients)
    return Trip(-1,-1,-1,[])

#Trips at the end and beginning of the different vehicle's availability intervals
def check_if_availability_trips_needed(curr_patient,curr_vehicle, trip_origin, prev_arrivalTime):
    return_and_initial_trips = []
    if veh_availabilities_end[curr_vehicle][1] != -1:
        if activity_start_time[curr_patient] >= veh_availabilities_end[curr_vehicle][0]:
            #Return trip to depot
            trip_destination = veh_ends[curr_vehicle]
            trip_arrivalTime = convert_mins_to_str(convert_str_to_mins(prev_arrivalTime) + distMatrix[trip_origin][trip_destination])
            trip_patients = []
            return_and_initial_trips.append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
            #Initial trip in next availability period
            trip_destination = trip_origin 
            trip_origin = veh_starts[curr_vehicle]
            trip_arrivalTime = convert_mins_to_str(activity_start_time[curr_patient])
            trip_patients = []
            return_and_initial_trips.append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
    return return_and_initial_trips
    
#Situations where patients have been dropped(removes them from next trip's patient list)                
def drop_patients(vehiclePatients, curr_patient_examined, trip_origin):
    dropped_patients = []
    for k in range(curr_patient_examined-2, -1, -1): 
        n = vehiclePatients[k]
        if trip_origin == activity_ends[n]: 
            dropped_patients.append(n)
    return dropped_patients



#---------------------------------------Minizinc result processing---------------------------------------



#Takes the sequence of actions obtained from minizinc and translates them into a sequence of trips
def result_to_trips(result):
    global requestsSatisfied, activity_start_time, activity_duration, activity_end_time, activity_vehicle, activity_completed
    global activity_starts, activity_ends, srvDurations, patientIDs, patientsWaiting
    
    requestsSatisfied = result['objective']
    activity_start_time = result['activity_start']
    activity_duration = result['activity_duration']
    activity_end_time = result['activity_end']
    activity_vehicle = result['activity_vehicle']
    activity_completed  = result['activity_completed']

    activity_starts = pat_starts + pat_destinations
    activity_ends = pat_destinations + pat_ends
    srvDurations = pat_srvDurations + pat_srvDurations
    patientIDs = pat_ids + pat_ids
    patientsWaiting = []

    firstCheck = True

    trip_origin, trip_destination, trip_arrivalTime = -1,-1,-1
    trip_patients = []
    trips = []

    #for every vehicle
    for i in range(num_vehicles):
        firstCheck = True
        trips.append([])
        vehicle = veh_ids[i]
        vehiclePatients, vehiclePatientsStartTimes = [], []

        #Get valid patients picked-up by vehicle i
        for j in range(num_activities): 
            if activity_vehicle[j] == vehicle and activity_completed[j] and activity_starts[j] != -1 and activity_ends[j] != -1: 
                vehiclePatients.append(j)
                vehiclePatientsStartTimes.append(activity_start_time[j])

        if len(vehiclePatients) == 0:
            continue
        
        #Sort chronologically patients associated to vehicle i
        vehiclesPatientsSorted = sort_vehicle_patients_chronologically(vehiclePatients,vehiclePatientsStartTimes)
        
        #first trip of vehicle i from depot to first patient
        trip_origin = veh_starts[i]
        trip_destination = activity_starts[vehiclesPatientsSorted[0]]
        trip_arrivalTime = convert_mins_to_str(activity_start_time[vehiclesPatientsSorted[0]])
        trip_patients = []
        trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
       
        #for every valid patient picked-up by vehicle i (Generating trips)
        for k in range(len(vehiclesPatientsSorted)): 
            n = vehiclesPatientsSorted[k] #Current patient (k) index
            n_before = 0
            if k != len(vehiclesPatientsSorted) - 1: 
                n_after = vehiclesPatientsSorted[k+1] #Following patient (k+1) index 
            if k != 0:
                n_before = vehiclesPatientsSorted[k-1] #Previous patient (k-1) index
            trip_origin = trips[i][-1].destination 

            #Check if vehicle needs to return to depot after availability period has ended
            return_and_initial_trips = check_if_availability_trips_needed(n,i, trip_origin, trips[i][-1].arrivalTime)
            if len(return_and_initial_trips) != 0 and firstCheck:
                trips[i].append(return_and_initial_trips[0])
                trips[i].append(return_and_initial_trips[1])
                firstCheck = False
            
            #Check if a trip without any patients is needed to go pickup current patient
            if k!=0:
                empty_trip = check_if_empty_trip_needed(n, n_before, trip_origin, trips[i][-1].arrivalTime)
                if(empty_trip.origin != -1):
                    trips[i].append(empty_trip)
                    trip_origin = empty_trip.destination
            

            #Heading to hospital or patient's home                                                                    
            if activity_end_time[n] - activity_start_time[n] == distMatrix[activity_starts[n]][activity_ends[n]]:
                trip_destination = activity_ends[n]
                trip_arrivalTime = convert_mins_to_str(activity_end_time[n] + srvDurations[n]) 
                if len(trips[i][-1].patients) == 0: #Transport only current patient
                    trip_patients = [patientIDs[n]]
                else:
                    if patientIDs[n] in trips[i][-1].patients: #Same patients as in last trip
                        trip_patients = trips[i][-1].patients
                    else:                                       #Same patients as in last trip + current patient
                        trip_patients = trips[i][-1].patients + [patientIDs[n]]
                    
                    #Check if any patient/s from last trip has/have been dropped
                    patients_to_drop = drop_patients(vehiclesPatientsSorted,k,trip_origin)
                    for patient_to_drop in patients_to_drop:
                        if patientIDs[patient_to_drop] in trip_patients:
                            trip_patients.remove(patientIDs[patient_to_drop])

                trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))

            #Picking up a patient at a different location than the current one
            elif (k != len(vehiclesPatientsSorted) - 1 and 
            activity_start_time[n_after] == activity_start_time[n] + distMatrix[trip_origin][activity_starts[n_after]] + srvDurations[n] 
            and trip_origin != activity_starts[n_after]):

                trip_destination = activity_starts[n_after]
                trip_arrivalTime = convert_mins_to_str(activity_start_time[n_after])
                if len(trips[i][-1].patients) == 0: #Transport only current patient
                    trip_patients = [patientIDs[n]] 
                else:
                    if(patientIDs[n] in trips[i][-1].patients): #Same patients as in last trip
                        trip_patients = trips[i][-1].patients
                    else:                                       #Same patients as in last trip + current patient
                        trip_patients = trips[i][-1].patients + [patientIDs[n]] 

                    #Check if any patient/s from last trip has/have been dropped
                    patients_to_drop = drop_patients(vehiclesPatientsSorted,k,trip_origin)
                    for patient_to_drop in patients_to_drop:
                        if(patientIDs[patient_to_drop] in trip_patients):
                            trip_patients.remove(patientIDs[patient_to_drop]) 
                    
                trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients))
             
            #Waiting at hospital for patients
            else:
                if len(patientsWaiting) != 0:
                    first = patientsWaiting[0] 

                #if not last patient to wait for                                                                               
                if len(patientsWaiting) == 0 or activity_end_time[first] - activity_start_time[n] != distMatrix[trip_origin][activity_ends[first]] + srvDurations[first] + srvDurations[n]:
                    patientsWaiting.append(n)
                #else return patients to their end location
                else:
                    patientsWaiting.append(n)
                    return_trips = obtain_return_trips_after_wait(trip_origin)
                    patientsWaiting = []
                    trips[i] = trips[i] + return_trips


        #Trip to return to depot
        trip_origin = trips[i][-1].destination
        trip_destination = veh_ends[i]
        trip_arrivalTime = convert_mins_to_str(convert_str_to_mins(trips[i][-1].arrivalTime) + distMatrix[trip_origin][veh_ends[i]] + srvDurations[n])
        trip_patients = []
        trips[i].append(Trip(trip_origin,trip_destination,trip_arrivalTime,trip_patients)) 



    return trips
        


#---------------------------------------Output writing---------------------------------------



def trips_to_output(outputFile, trips, requestsSatisfied):
    output_dict = {"requests": requestsSatisfied}
    vehicles_list, trip_list = [], []
    for i in range(len(trips)):
        vehicle_dict = {}
        vehicle_dict = {'id': veh_ids[i]} 
        for trip in trips[i]:
            trip_dict = {}
            trip_dict["origin"] = trip.origin
            trip_dict["destination"] = trip.destination
            trip_dict["arrival"] = trip.arrivalTime
            trip_dict["patients"] = trip.patients
            trip_list.append(trip_dict)
        vehicle_dict["trips"] = trip_list
        vehicles_list.append(vehicle_dict)
        trip_list = []

    output_dict['vehicles'] = vehicles_list

    json_object = json.dumps(output_dict, indent = 1)
    with open(outputFile, 'w') as file:
        file.write(json_object)
    
    

#---------------------------------------Minizinc model initialization-------------------------------------------------



def initialize_locations(input_data, ptpInstance):
    global loc_ids, loc_categories # = [], []
    loc_ids, loc_categories = [], []
    for location in input_data['places']:
        loc_ids.append(location['id'])
        loc_categories.append(location['category'])
    ptpInstance['location_id'] = loc_ids
    ptpInstance['location_category'] = loc_categories


def initialize_vehicles(input_data, ptpInstance):
    global veh_ids, veh_canTakes, veh_starts, veh_ends, veh_capacities, veh_availabilities_start, veh_availabilities_end, first_vehicle_id
    veh_ids, veh_canTakes, veh_starts, veh_ends, veh_capacities, veh_availabilities_start, veh_availabilities_end = [], [], [], [], [], [], []
    canTakeMax, availabilitiesMax, i, first_vehicle = 0, 0, 0, 0
    for vehicle in input_data['vehicles']:
        if(i==0):
            first_vehicle_id = vehicle['id']
        veh_availabilities_start.append([])
        veh_availabilities_end.append([])
        veh_ids.append(vehicle['id'])
        veh_canTakes.append(vehicle['canTake']) 
        veh_starts.append((vehicle['start']))
        veh_ends.append((vehicle['end']))
        veh_capacities.append(vehicle['capacity'])
        for availability_interval in vehicle['availability']:
            interval_elements = availability_interval.split(':')
            veh_availabilities_start[i].append(convert_str_to_mins(interval_elements[0]))
            veh_availabilities_end[i].append(convert_str_to_mins(interval_elements[1]))
        i = i + 1
    for j in range(len(veh_canTakes)):
        while len(veh_canTakes[j]) != 3: 
            veh_canTakes[j].append(-1)
            
    for k in range(len(veh_availabilities_start)):
        while len(veh_availabilities_start[k]) != 2: 
            veh_availabilities_start[k].append(-1)
            veh_availabilities_end[k].append(-1)

    ptpInstance['vehicle_id'] = veh_ids
    ptpInstance['num_canTake'] = 3 
    ptpInstance['vehicle_canTake'] = veh_canTakes
    ptpInstance['vehicle_start_location'] = veh_starts
    ptpInstance['vehicle_end_location'] = veh_ends
    ptpInstance['vehicle_capacity'] = veh_capacities
    ptpInstance['num_availability'] = 2 
    ptpInstance['vehicle_availability_start'] = veh_availabilities_start
    ptpInstance['vehicle_availability_end'] = veh_availabilities_end


def initialize_patients(input_data, ptpInstance):
    global pat_ids, pat_categories, pat_loads, pat_starts, pat_destinations, pat_ends, pat_rdvTimes, pat_rdvDurations, pat_srvDurations
    pat_ids, pat_categories, pat_loads, pat_starts, pat_destinations, pat_ends, pat_rdvTimes, pat_rdvDurations, pat_srvDurations = [], [], [], [], [], [], [], [], []
    for patient in input_data['patients']:
        pat_ids.append(patient['id'])
        pat_categories.append(patient['category'])
        pat_loads.append(patient['load'])
        pat_starts.append(patient['start'])
        pat_destinations.append(patient['destination'])
        pat_ends.append(patient['end'])
        pat_rdvTimes.append(convert_str_to_mins(patient['rdvTime']))
        pat_rdvDurations.append(convert_str_to_mins(patient['rdvDuration']))
        pat_srvDurations.append(convert_str_to_mins(patient['srvDuration']))

    ptpInstance['patient_id'] = pat_ids
    ptpInstance['patient_category'] = pat_categories
    ptpInstance['patient_load'] = pat_loads
    ptpInstance['patient_start_location'] = pat_starts
    ptpInstance['patient_destination'] = pat_destinations
    ptpInstance['patient_end_location'] = pat_ends
    ptpInstance['rdvTime'] = pat_rdvTimes
    ptpInstance['rdvDuration'] = pat_rdvDurations
    ptpInstance['srvDuration'] = pat_srvDurations



def initialize_model(input_data, ptpInstance):
    global sameVehicleBackward, maxWaitTime, num_locations, num_vehicles, num_patients, num_activities, distMatrix

    sameVehicleBackward = input_data['sameVehicleBackward']
    maxWaitTime = convert_str_to_mins(input_data['maxWaitTime'])
    num_locations = len(input_data['places'])
    num_vehicles = len(input_data['vehicles'])
    num_patients = len(input_data['patients'])
    num_activities = num_patients * 2
    distMatrix = input_data['distMatrix']

    ptpInstance['sameVehicleBackward'] = sameVehicleBackward
    ptpInstance['maxWaitTime'] = maxWaitTime
    ptpInstance['num_locations'] = num_locations
    ptpInstance['num_vehicles'] = num_vehicles
    ptpInstance['num_patients'] = num_patients


    initialize_locations(input_data, ptpInstance)
    initialize_vehicles(input_data, ptpInstance)
    initialize_patients(input_data, ptpInstance)

    ptpInstance['distMatrix'] = input_data['distMatrix']





def main():
    if len(sys.argv) != 3:
        sys.stderr.write("There must be two arguments: python proj.py <input-file-name> <output-file-name>")
        exit()

    gecode = Solver.lookup("gecode")
    ptpModel = Model("./projModel.mzn")
    ptpInstance = Instance(gecode, ptpModel)
    
    with open(sys.argv[1], "r") as input_file:
        input_data = json.load(input_file)

    initialize_model(input_data, ptpInstance)

    result = ptpInstance.solve()

    if(len(result) == 0):
        with open(sys.argv[2], 'w') as file:
            json.dump(["No solution found"], file)
        exit()
    trips = result_to_trips(result)
    trips_to_output(sys.argv[2],trips,result['objective'])

    

if __name__ == "__main__":
    main()