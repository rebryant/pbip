!/bin/sh
python3 ../../tools/pbip_drive.py -x -m s -t 1000 -l files-sc.txt
python3 ../../tools/pbip_drive.py -x -m s -t 1000 -l files-sn.txt
python3 ../../tools/pbip_drive.py -x -m s -t 1000 -l files-tz.txt

python3 ../../tools/pbip_drive.py -x -m b -t 1000 -l files-sc.txt
python3 ../../tools/pbip_drive.py -x -m b -t 1000 -l files-sn.txt
python3 ../../tools/pbip_drive.py -x -m b -t 1000 -l files-tz.txt


