import re
import os


def read_results(result_directory):
  results = []
  for file in os.listdir(result_directory):
    f = open(os.path.join(result_directory, file), "r")
    content = f.read()
    result = re.search(r"encoding time: (\d+.\d+), solving time (\d+.\d+), total time (\d+.\d+)", content)
    enc_time = float(result.group(1))
    solve_time = float(result.group(2))
    total_time = float(result.group(3))
    result = re.search(r"distance (\d+)", content)
    distance = float(result.group(1))
    result = re.search(r"#events (\d+), #objects (\d+)", content)
    events = float(result.group(1))
    objects = float(result.group(2))
    results.append({
      "encoding time": enc_time, 
      "solving time": solve_time,
      "total time": total_time,
      "distance": distance, 
      "events": events,
      "objects": objects
    })
  return results

def write_stats_file(results, key, value, filename):
  content = ""
  for r in results:
    content += "%d %.2f\n" % (r[key], r[value])
  f = open(filename, "w")
  f.write(content)
  f.close()


def write_distance_vs_time(results):
  filename = "stats/distance_vs_time.dat"
  write_stats_file(results, "distance", "total time", filename)

def write_events_vs_time(results):
  filename = "stats/events_vs_time.dat"
  write_stats_file(results, "events", "total time", filename)

def write_objects_vs_time(results):
  filename = "stats/objects_vs_time.dat"
  write_stats_file(results, "objects", "total time", filename)

def compute_aggregates(results):
  avg = lambda xs: sum(xs)/float(len(xs))
  distances = [r["distance"] for r in results]
  total_times = [r["total time"] for r in results]
  objects = [r["objects"] for r in results]
  events = [r["events"] for r in results]
  print("distance max %d avg %.2f" % (max(distances), avg(distances)))
  print("objects max %d avg %.2f" % (max(objects), avg(objects)))
  print("events max %d avg %.2f" % (max(events), avg(events)))
  print("total time max %.2f avg %.2f" % (max(total_times), avg(total_times)))

if __name__ == "__main__":
  results = read_results("./cllabws_out_fixed_objects_0812")
  write_distance_vs_time(results)
  write_events_vs_time(results)
  write_objects_vs_time(results)
  compute_aggregates(results)
