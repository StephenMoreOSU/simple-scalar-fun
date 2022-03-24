#!/usr/bin/python3

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
import re
import csv

import glob


data_path = "./sim_oo_outputs/"

sim_stats = ["global_num_0_deps", "global_num_1_deps", "global_num_2_deps"]

width = 0.4

color_list = ['r', 'g', 'b']

bm_bar_data = []

for fname in glob.glob(data_path+"/*.txt"):
    file = open(fname,"r")
    for line in file:
        for stat,stat_color in zip(sim_stats,color_list):
            if re.search(stat,line):
                match_list = re.split(r'\s{1,}',line)[0:2]
                print(match_list)
                bm_bar_data.append(int(match_list[1]))
                # p1 = plt.bar(0,np.array(match_list[1]), width, stat_color,)

fig, ax = plt.subplots()

ax.bar("test_label", bm_bar_data[0],width, color='r', label=sim_stats[0])
ax.bar("test_label", bm_bar_data[1],width, color='g', label=sim_stats[1],bottom=bm_bar_data[0])

ax.legend()

plt.savefig("test.png")


