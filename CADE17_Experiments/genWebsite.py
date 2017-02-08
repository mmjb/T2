#!/usr/bin/env python
'''
Usage:
    genWebsite.py [options] T2LOG APROVELOG CETALOG EXPDATADIR EXAMMPLEDIR TARGETDIR

Options:
    -h --help                Show this screen.
'''
from __future__ import print_function
import csv
import os
import pdb
import shutil
import sys
import subprocess
import traceback
import ntpath
from collections import defaultdict
from docopt import docopt

CETA_TIMEOUT = 60.0
PROVER_TIMEOUT = 60.0

def mean(numbers):
    return float(sum(numbers)) / max(len(numbers), 1)

def colour_result(res):
    if res == "YES" or res == "CERTIFIED":
        return '<span class="YES">%s</span>' % res
    elif res == "NO" or res == "REJECTED":
        return '<span class="NO">%s</span>' % res
    else:
        return res

def run(args):
    target_dir=args['TARGETDIR']
    target_data_dir=os.path.join(args['TARGETDIR'], 'data')
    if not(os.path.isdir(target_dir)):
        os.makedirs(target_dir)
    if not(os.path.isdir(target_data_dir)):
        os.makedirs(target_data_dir)

    ceta_results = {}
    with open(args['CETALOG'], 'rb') as f:
        fieldnames=['CertPath', 'CertWinPath',
                    'CeTARes', 'CeTATime']
        data = csv.DictReader(f, fieldnames=fieldnames, delimiter=';')
        for row in data:
            ceta_results[row['CertPath']] = (row['CeTARes'], float(row['CeTATime']))

    results = defaultdict(lambda: defaultdict(dict))
    with open(args['T2LOG'], 'rb') as f:
        fieldnames=['name',
                    'T2CertRes', 'T2CertTime', 'T2CertCertPath',
                    'T2CertHintingRes', 'T2CertHintingTime', 'T2CertHintingCertPath',
                    'T2FullRes', 'T2FullTime']
        data = csv.DictReader(f, fieldnames=fieldnames, delimiter=';')
        for row in data:
            # Copy example into linkable place:
            example_filename = row['name']
            orig_example_filename = example_filename[:-3]
            orig_example_name = orig_example_filename
            final_orig_example_path = os.path.join(target_data_dir, orig_example_name.replace('/', '__'))
            shutil.copyfile(os.path.join(args['EXDIR'], orig_example_filename),
                            final_orig_example_path)

            # Extract the interesting information:            
            for prover_name in ['T2Cert', 'T2CertHinting', 'T2Full']:
                prover_time = float(row[prover_name + 'Time'])
                prover_res = row[prover_name + 'Res']
                if prover_time > PROVER_TIMEOUT:
                    prover_time = PROVER_TIMEOUT
                    prover_res = 'TIMEOUT'
                results[orig_example_name][prover_name]['result'] = prover_res
                results[orig_example_name][prover_name]['time'] = prover_time

            # Extract string for table + possibly certificate:
            for (prover_name, certifier_name) in [('T2Cert', 'CeTA'), ('T2CertHinting', 'CeTAHinted')]:
                prover_result = results[orig_example_name][prover_name]['result']
                prover_time = results[orig_example_name][prover_name]['time']
                if prover_result == 'YES':
                    # Copy certificate + render it:
                    cert_path = row[prover_name + 'CertPath']
                    final_cert_filename = orig_example_name.replace('/', '__') + '.' + prover_name + '_' + certifier_name + '.xml'
                    final_cert_path = os.path.join(target_data_dir, final_cert_filename)
                    shutil.copyfile(cert_path, final_cert_path)
                    final_cert_html_filename = orig_example_name.replace('/', '__') + '.' + prover_name + '_' + certifier_name + '.html'
                    final_cert_html_path = os.path.join(target_data_dir, final_cert_html_filename)
                    subprocess.check_call(['xsltproc',
                                           '--output',
                                           final_cert_html_path,
                                           '../cetaITS/cpfHTML.xsl',
                                           final_cert_path])

                    cert_name = ntpath.basename(cert_path)
                    (cert_result, cert_time) = ceta_results[cert_name]
                    if cert_time > CETA_TIMEOUT:
                        cert_time = CETA_TIMEOUT
                        cert_result = "TIMEOUT"
                    else:
                        if cert_result not in ["CERTIFIED", "REJECTED"]:
                            cert_result = "ERROR"

                    results[orig_example_name][prover_name]['html'] = \
                                '%s (%.2fs) (certificate <a href="data/%s">CPF</a> <a href="data/%s">HTML</a>)<br/>%s (%.2fs)' \
                                % (colour_result(prover_result),
                                   prover_time,
                                   final_cert_filename,
                                   final_cert_html_filename,
                                   colour_result(cert_result),
                                   cert_time)
                    results[orig_example_name][prover_name]['cert_result'] = cert_result
                    results[orig_example_name][prover_name]['cert_time'] = cert_time
                else:
                    results[orig_example_name][prover_name]['html'] = \
                                '%s (%.2fs)<br/>' \
                                % (colour_result(prover_result),
                                   prover_time)
                    results[orig_example_name][prover_name]['cert_result'] = ''
                    results[orig_example_name][prover_name]['cert_time'] = 0
            # Extract data for uncertified:
            for prover_name in ['T2Full']:
                prover_result = results[orig_example_name][prover_name]['result']
                prover_time = results[orig_example_name][prover_name]['time']
                results[orig_example_name][prover_name]['html'] = \
                                '%s (%.2fs)<br/>' \
                                % (colour_result(prover_result),
                                   prover_time)
                results[orig_example_name][prover_name]['cert_result'] = ''
                results[orig_example_name][prover_name]['cert_time'] = 0

    with open(args['APROVELOG'], 'rb') as f:
        fieldnames=['name',
                    'AProVECertRes', 'AProVECertTime', 'AProVECertCertPath'
                    'AProVEFullRes', 'AProVEFullTime',]
        data = csv.DictReader(f, fieldnames=fieldnames, delimiter=';')
        for row in data:
            # Copy example into linkable place:
            example_filename = row['name']
            orig_example_filename = example_filename[:-7]
            orig_example_name = orig_example_filename
            final_orig_example_path = os.path.join(target_data_dir, orig_example_name.replace('/', '__'))
            shutil.copyfile(os.path.join(args['EXDIR'], orig_example_filename),
                            final_orig_example_path)

            # Extract the interesting information:            
            for prover_name in ['AProVECert', 'AProVEFull']:
                prover_time = float(row[prover_name + 'Time'])
                prover_res = row[prover_name + 'Res']
                if prover_time > PROVER_TIMEOUT:
                    prover_time = PROVER_TIMEOUT
                    prover_res = 'TIMEOUT'
                results[orig_example_name][prover_name]['result'] = prover_res
                results[orig_example_name][prover_name]['time'] = prover_time

            # Extract string for table + possibly certificate:
            for (prover_name, certifier_name) in [('AProVECert', 'CeTA')]:
                prover_result = results[orig_example_name][prover_name]['result']
                prover_time = results[orig_example_name][prover_name]['time']
                if prover_result == 'YES':
                    # Copy certificate + render it:
                    cert_path = row[prover_name + 'CertPath']
                    final_cert_filename = orig_example_name.replace('/', '__') + '.' + prover_name + '_' + certifier_name + '.xml'
                    final_cert_path = os.path.join(target_data_dir, final_cert_filename)
                    shutil.copyfile(cert_path, final_cert_path)
                    final_cert_html_filename = orig_example_name.replace('/', '__') + '.' + prover_name + '_' + certifier_name + '.html'
                    final_cert_html_path = os.path.join(target_data_dir, final_cert_html_filename)
                    subprocess.check_call(['xsltproc',
                                           '--output',
                                           final_cert_html_path,
                                           '../cetaITS/cpfHTML.xsl',
                                           final_cert_path])

                    cert_name = ntpath.basename(cert_path)
                    (cert_result, cert_time) = ceta_results[cert_name]
                    if cert_time > CETA_TIMEOUT:
                        cert_time = CETA_TIMEOUT
                        cert_result = "TIMEOUT"
                    else:
                        if cert_result not in ["CERTIFIED", "REJECTED"]:
                            cert_result = "ERROR"

                    results[orig_example_name][prover_name]['html'] = \
                                '%s (%.2fs) (certificate <a href="data/%s">CPF</a> <a href="data/%s">HTML</a>)<br/>%s (%.2fs)' \
                                % (colour_result(prover_result),
                                   prover_time,
                                   final_cert_filename,
                                   final_cert_html_filename,
                                   colour_result(cert_result),
                                   cert_time)
                    results[orig_example_name][prover_name]['cert_result'] = cert_result
                    results[orig_example_name][prover_name]['cert_time'] = cert_time
                else:
                    results[orig_example_name][prover_name]['html'] = \
                                '%s (%.2fs)<br/>' \
                                % (colour_result(prover_result),
                                   prover_time)
                    results[orig_example_name][prover_name]['cert_result'] = ''
                    results[orig_example_name][prover_name]['cert_time'] = 0
            # Extract data for uncertified:
            for prover_name in ['AProVEFull']:
                prover_result = results[orig_example_name][prover_name]['result']
                prover_time = results[orig_example_name][prover_name]['time']
                results[orig_example_name][prover_name]['html'] = \
                                '%s (%.2fs)<br/>' \
                                % (colour_result(prover_result),
                                   prover_time)
                results[orig_example_name][prover_name]['cert_result'] = ''
                results[orig_example_name][prover_name]['cert_time'] = 0
                
    with open(os.path.join(args['TARGETDIR'], 'res_table.html'), 'w') as out:
        print(' <h2>Result overview</h2>', file=out)
        print(' <table border="1">', file=out)
        print('  <tr>', file=out)
        print('   <th border="0"></th>', file=out)
        print('   <th>YES (CERTIFIED)</th>', file=out)
        print('   <th>YES (REJECTED)</th>', file=out)
        print('   <th>YES (CeTA Error)</th>', file=out)
        print('   <th>YES (CeTA Timeout)</th>', file=out)        
        print('   <th>YES</th>', file=out)              
        print('   <th>NO</th>', file=out)
        print('   <th>MAYBE</th>', file=out)
        print('   <th>TIMEOUT</th>', file=out)        
        print('  </tr>', file=out)

        # Build and print aggregate data:
        results_by_prover = defaultdict(dict)
        for prover_name in ['T2Cert', 'T2CertHinting', 'AProVECert', 'T2Full', 'AProVEFull']:
            times_by_result = defaultdict(lambda: ([], []))
            all_prover_times = []
            all_ceta_times = []
            for example in results.keys():
                full_result = (results[example][prover_name]['result'],
                               results[example][prover_name]['cert_result'])
                times_by_result[full_result][0].append(results[example][prover_name]['time'])
                times_by_result[full_result][1].append(results[example][prover_name]['cert_time'])
                all_prover_times.append(results[example][prover_name]['time'])
                if results[example][prover_name]['result'] == 'YES':
                    all_ceta_times.append(results[example][prover_name]['cert_time'])

            result_types = times_by_result.keys()
            print("%s prover: results: %s" % (prover_name, ", ".join(map(str, result_types))))
            print("           avg. time %.2fs, avg. time certification: %.2fs" % (mean(all_prover_times), mean(all_ceta_times)))
            known_result_types = [('YES', 'CERTIFIED'), ('YES', 'REJECTED'), ('YES', 'ERROR'), ('YES', 'TIMEOUT'),
                                  ('YES', ''), ('NO', ''), ('MAYBE', ''), ('TIMEOUT', '')]
            for result_type in result_types:
                assert(result_type in known_result_types)

            print('  <tr>', file=out)
            print('   <th align="left">%s</th>' % prover_name, file=out)
            for (prover_result, cert_result) in known_result_types:
                if cert_result != '':
                    print('   <td>%i (avg. %.2fs prover, avg. %.2fs CeTA)</td>'\
                          % (len(times_by_result[(prover_result, cert_result)][0]),
                             mean(times_by_result[(prover_result, cert_result)][0]),
                             mean(times_by_result[(prover_result, cert_result)][1])),
                          file=out)
                else:
                    print('   <td>%i (avg. %.2fs prover)</td>'\
                          % (len(times_by_result[(prover_result, cert_result)][0]),
                             mean(times_by_result[(prover_result, cert_result)][0])),
                          file=out)
            print('  </tr>', file=out)
        print(' </table>', file=out)

        
        print(' <h2>Detailed results</h2>', file=out)
        print(' <table>', file=out)
        print('  <tr>', file=out)
        print('   <th>Example Name</th>', file=out)
        for prover_name in ['T2Cert', 'T2CertHinting', 'T2Full', 'AProVECert', 'AProVEFull']:                  
            print('   <th>%s</th>' % prover_name, file=out)
        print('  </tr>', file=out)

        for (ex_name, per_prover) in sorted(results.iteritems(), key=lambda t:t[0]):
            print('  <tr>', file=out)
            print('   <th align="left"><a href="%s">%s</a></th>' % (final_orig_example_path, ex_name), file=out)
            for prover_name in ['T2Cert', 'T2CertHinting', 'T2Full', 'AProVECert', 'AProVEFull']:
                print('   <td>%s</td>' % (per_prover[prover_name]['html']), file=out)
            print('  </tr>', file=out)
        print(' </table>', file=out)

if __name__ == "__main__":
    args = docopt(__doc__)
    try:
        run(args)
    except:
        type, value, tb = sys.exc_info()
        traceback.print_exc()
        pdb.post_mortem(tb)
